-- Prove2me | Theorems.Thm_GlobalTheory_GaussExpSeries_exists_bound_poly_mul_exp
-- name    : GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:14.274528+00:00
-- url     : https://prove2.me/theorems/3a2b1d4d-0d70-4475-9946-9128f51bcd85
-- title:
--   Gauss Exp Series: exists bound poly mul exp
-- statement:
--   The Gauss Exp Series construction uses the exists bound poly mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivTruncExpICompLe.lean#L75-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Nat
noncomputable section
open GlobalTheory GlobalTheory.GaussExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by sorry
