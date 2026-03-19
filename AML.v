(******************************************************************************)
(*                                                                            *)
(*                  Anti-Money Laundering Transaction Rules                   *)
(*                                                                            *)
(*     Suspicious activity detection: structuring, rapid movement, layering,  *)
(*     and threshold reporting per FATF and FinCEN. Models the pattern-       *)
(*     matching logic that triggers Suspicious Activity Reports.              *)
(*                                                                            *)
(*     Follow the money.                                                      *)
(*     (All the President's Men, 1976)                                        *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: TRANSACTION TYPES AND CUSTOMERS                                *)
(******************************************************************************)

Inductive TransactionType : Type :=
  | CashDeposit
  | CashWithdrawal
  | WireTransfer
  | CheckDeposit
  | ACHTransfer
  | CurrencyExchange
  | CashierCheck
  | MoneyOrder.

(* Customer due diligence risk tier *)
Inductive RiskTier : Type :=
  | Low
  | Medium
  | High
  | PEP.   (* Politically Exposed Person — enhanced due diligence *)

(* A transaction record *)
Record Transaction : Type := mkTx {
  tx_amount      : nat;    (* amount in cents *)
  tx_type        : TransactionType;
  tx_day         : nat;    (* day number since epoch *)
  tx_risk_tier   : RiskTier;
  tx_structured  : bool;   (* flagged as possible structuring *)
}.

(******************************************************************************)
(* SECTION 2: CTR THRESHOLD — 31 CFR § 103.22                               *)
(******************************************************************************)

(* Currency Transaction Report (CTR): required for cash transactions > $10,000.
   Amount in cents: $10,000 = 1,000,000 cents *)

Definition ctr_threshold_cents : nat := 1000000.

Definition ctr_required (tx : Transaction) : bool :=
  match tx_type tx with
  | CashDeposit | CashWithdrawal | CurrencyExchange =>
      Nat.ltb ctr_threshold_cents (tx_amount tx)
  | _ => false
  end.

Theorem ctr_at_threshold_not_required : forall tx,
  tx_type tx = CashDeposit ->
  tx_amount tx = ctr_threshold_cents ->
  ctr_required tx = false.
Proof.
  intros tx Htype Hamount.
  unfold ctr_required. rewrite Htype. rewrite Hamount.
  apply Nat.ltb_irrefl.
Qed.

Theorem ctr_above_threshold_required : forall tx,
  tx_type tx = CashDeposit ->
  tx_amount tx > ctr_threshold_cents ->
  ctr_required tx = true.
Proof.
  intros tx Htype Hamount.
  unfold ctr_required. rewrite Htype.
  apply Nat.ltb_lt. exact Hamount.
Qed.

(******************************************************************************)
(* SECTION 3: STRUCTURING — 31 U.S.C. § 5324                                *)
(******************************************************************************)

(* Structuring: breaking transactions into amounts below $10,000 to evade CTR.
   We detect structuring if multiple same-day transactions each below threshold
   but together exceed the threshold. *)

Definition structuring_threshold_cents : nat := 1000000.

(* Sum of a list of transaction amounts *)
Fixpoint total_amount (txs : list Transaction) : nat :=
  match txs with
  | []      => 0
  | t :: ts => tx_amount t + total_amount ts
  end.

(* All individual transactions below threshold *)
Definition all_below_threshold (txs : list Transaction) : bool :=
  forallb (fun tx => Nat.leb (tx_amount tx) structuring_threshold_cents) txs.

(* Structuring pattern: each transaction is at or below the threshold,
   but the total exceeds it *)
Definition structuring_detected (txs : list Transaction) : bool :=
  all_below_threshold txs &&
  Nat.ltb structuring_threshold_cents (total_amount txs) &&
  Nat.leb 2 (length txs).

(* Two transactions each just below threshold that sum above it = structuring *)
Lemma two_below_summing_above_is_structuring :
  let tx1 := mkTx 900000 CashDeposit 1 Low false in
  let tx2 := mkTx 900000 CashDeposit 1 Low false in
  structuring_detected [tx1; tx2] = true.
Proof. reflexivity. Qed.

(* A single transaction below threshold cannot be structuring *)
Theorem single_tx_not_structuring : forall tx,
  tx_amount tx <= structuring_threshold_cents ->
  structuring_detected [tx] = false.
Proof.
  intros tx H.
  unfold structuring_detected. simpl.
  rewrite andb_false_r. reflexivity.
Qed.

(* More transactions increase total (monotonicity) *)
Lemma total_amount_cons : forall tx txs,
  total_amount (tx :: txs) = tx_amount tx + total_amount txs.
Proof. intros tx txs. reflexivity. Qed.

Theorem total_amount_non_negative : forall txs,
  total_amount txs >= 0.
Proof. intros txs. lia. Qed.

(******************************************************************************)
(* SECTION 4: SAR TRIGGERS — FATF RECOMMENDATION 20                         *)
(******************************************************************************)

(* Suspicious Activity Report triggers *)
Inductive SARTrigger : Type :=
  | StructuringPattern
  | RapidMovement        (* funds moved quickly in and out *)
  | LayeringDetected     (* complex chain of transfers to obscure source *)
  | UnusualCashActivity
  | HighRiskCustomer
  | PEPTransaction
  | SanctionedCountry.

(* Each trigger has a risk score *)
Definition sar_trigger_score (t : SARTrigger) : nat :=
  match t with
  | StructuringPattern   => 80
  | RapidMovement        => 60
  | LayeringDetected     => 90
  | UnusualCashActivity  => 50
  | HighRiskCustomer     => 40
  | PEPTransaction       => 70
  | SanctionedCountry    => 100
  end.

Definition sar_threshold_score : nat := 70.

(* SAR is filed if combined trigger score exceeds threshold *)
Definition sar_required (triggers : list SARTrigger) : bool :=
  Nat.leb sar_threshold_score
    (fold_right (fun t acc => sar_trigger_score t + acc) 0 triggers).

Theorem sanctioned_country_alone_triggers_sar :
  sar_required [SanctionedCountry] = true.
Proof. reflexivity. Qed.

Theorem layering_alone_triggers_sar :
  sar_required [LayeringDetected] = true.
Proof. reflexivity. Qed.

Theorem low_score_no_sar :
  sar_required [HighRiskCustomer] = false.
Proof. reflexivity. Qed.

(* Combined triggers can push total over threshold *)
Theorem combined_triggers_can_trigger_sar :
  sar_required [RapidMovement; HighRiskCustomer] = true.
Proof. reflexivity. Qed.

(* Score is monotone: adding a trigger never decreases total *)
Theorem adding_trigger_nondecreasing : forall triggers t,
  fold_right (fun x acc => sar_trigger_score x + acc) 0 triggers <=
  fold_right (fun x acc => sar_trigger_score x + acc) 0 (t :: triggers).
Proof.
  intros triggers t. simpl. lia.
Qed.

(******************************************************************************)
(* SECTION 5: RAPID MOVEMENT DETECTION                                        *)
(******************************************************************************)

(* Rapid movement: funds deposited and withdrawn within a short window (e.g., 3 days) *)
Definition rapid_movement_window : nat := 3.

Definition same_window (day1 day2 : nat) : bool :=
  Nat.leb (day1 - day2) rapid_movement_window ||
  Nat.leb (day2 - day1) rapid_movement_window.

Definition rapid_movement_detected
    (deposit_day withdrawal_day : nat) (amount : nat) : bool :=
  same_window deposit_day withdrawal_day &&
  Nat.ltb 100000 amount.  (* $1,000 minimum to flag *)

Lemma same_day_is_rapid : forall day amount,
  amount > 100000 ->
  rapid_movement_detected day day amount = true.
Proof.
  intros day amount H.
  unfold rapid_movement_detected, same_window.
  rewrite Nat.sub_diag.
  assert (Hlt : Nat.ltb 100000 amount = true) by (apply Nat.ltb_lt; lia).
  rewrite Hlt. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 6: CUSTOMER RISK SCORING                                           *)
(******************************************************************************)

(* Customer risk score is a sum of risk factors *)
Record CustomerProfile : Type := mkCustomer {
  cp_is_pep               : bool;
  cp_high_risk_country    : bool;
  cp_cash_intensive_biz   : bool;
  cp_prior_sar            : bool;
  cp_kyc_complete         : bool;
}.

Definition customer_risk_score (p : CustomerProfile) : nat :=
  (if cp_is_pep p            then 40 else 0) +
  (if cp_high_risk_country p  then 30 else 0) +
  (if cp_cash_intensive_biz p then 20 else 0) +
  (if cp_prior_sar p          then 30 else 0) +
  (if negb (cp_kyc_complete p) then 20 else 0).

Definition high_risk_threshold : nat := 60.

Definition customer_high_risk (p : CustomerProfile) : bool :=
  Nat.leb high_risk_threshold (customer_risk_score p).

(* PEP with incomplete KYC is always high risk *)
Theorem pep_no_kyc_high_risk : forall p,
  cp_is_pep p = true ->
  cp_kyc_complete p = false ->
  customer_high_risk p = true.
Proof.
  intros p Hpep Hkyc.
  unfold customer_high_risk, customer_risk_score.
  rewrite Hpep, Hkyc. simpl.
  destruct (cp_high_risk_country p);
  destruct (cp_cash_intensive_biz p);
  destruct (cp_prior_sar p);
  simpl; lia.
Qed.

(* Low-risk customer with complete KYC and no flags *)
Theorem clean_profile_low_risk : forall p,
  cp_is_pep p = false ->
  cp_high_risk_country p = false ->
  cp_cash_intensive_biz p = false ->
  cp_prior_sar p = false ->
  cp_kyc_complete p = true ->
  customer_high_risk p = false.
Proof.
  intros p H1 H2 H3 H4 H5.
  unfold customer_high_risk, customer_risk_score.
  rewrite H1, H2, H3, H4, H5. simpl. reflexivity.
Qed.

(* Risk score is always non-negative *)
Theorem risk_score_non_negative : forall p,
  customer_risk_score p >= 0.
Proof. intros p. lia. Qed.

(******************************************************************************)
(* SECTION 7: TRANSACTION MONITORING RULES                                    *)
(******************************************************************************)

(* A transaction requires enhanced monitoring if:
   - Customer is high risk, OR
   - CTR is required, OR
   - Structuring is detected *)

Definition enhanced_monitoring_required
    (p : CustomerProfile)
    (tx : Transaction)
    (same_day_txs : list Transaction) : bool :=
  customer_high_risk p ||
  ctr_required tx ||
  structuring_detected same_day_txs.

Theorem high_risk_customer_triggers_monitoring : forall p tx txs,
  customer_high_risk p = true ->
  enhanced_monitoring_required p tx txs = true.
Proof.
  intros p tx txs H.
  unfold enhanced_monitoring_required. rewrite H. reflexivity.
Qed.

Theorem ctr_transaction_triggers_monitoring : forall p tx txs,
  ctr_required tx = true ->
  enhanced_monitoring_required p tx txs = true.
Proof.
  intros p tx txs H.
  unfold enhanced_monitoring_required. rewrite H. rewrite orb_true_r. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 8: SUMMARY                                                         *)
(******************************************************************************)

(*
  This file formalizes Anti-Money Laundering detection rules.

  Structure:
    1. Transaction types and risk tiers (Low/Medium/High/PEP).
    2. CTR threshold: cash transactions > $10,000 require Currency Transaction Report.
    3. Structuring detection: multiple sub-threshold transactions summing above threshold.
    4. SAR triggers: 7 trigger types with risk scores; SAR filed when total >= 70.
    5. Rapid movement: deposit and withdrawal within 3-day window.
    6. Customer risk scoring: 5-factor score; PEP + no KYC = high risk.
    7. Transaction monitoring: enhanced monitoring when customer high risk, CTR,
       or structuring detected.

  Key theorems:
    - ctr_at_threshold_not_required: $10,000 exactly does NOT trigger CTR.
    - ctr_above_threshold_required: >$10,000 triggers CTR.
    - two_below_summing_above_is_structuring.
    - single_tx_not_structuring: one transaction cannot be structuring.
    - sanctioned_country_alone_triggers_sar.
    - adding_trigger_nondecreasing: score is monotone.
    - pep_no_kyc_high_risk.
    - clean_profile_low_risk.
    - high_risk_customer_triggers_monitoring.

  All proofs closed; no Admitted lemmas.
*)
