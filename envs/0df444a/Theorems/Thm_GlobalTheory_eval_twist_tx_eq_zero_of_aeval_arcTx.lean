-- Prove2me | Theorems.Thm_GlobalTheory_eval_twist_tx_eq_zero_of_aeval_arcTx
-- name    : GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:36.97498+00:00
-- url     : https://prove2.me/theorems/7f9eafec-279d-5809-918e-d1f294e42fe7
-- title:
--   Global Theory: eval twist tx eq zero of aeval arc Tx
-- statement:
--   The Global Theory construction uses the eval twist tx eq zero of aeval arc Tx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L348-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L348-L362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open scoped BigOperators

theorem GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx : ∀ (C : Type) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] (N : _root_.GlobalTheory.Ex.NumD C) (k : ℕ)
    (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m →
    ∀ (ι : Type) (p : ι → N.QT (m ^ 2)),
    (∀ i χ, ‖N.txT m (p i) χ‖ ≤ 1) → ∀ (F : MvPolynomial ι C),
    MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 →
    ∀ u : Cˣ, ‖(u : C)‖ < 1 →
    MvPolynomial.eval (fun i => (N.twist β u).tx m
      (N.twQ β u hm (p i))) F = 0 := by sorry
