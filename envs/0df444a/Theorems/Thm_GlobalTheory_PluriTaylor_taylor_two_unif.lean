-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_taylor_two_unif
-- name    : GlobalTheory.PluriTaylor.taylor_two_unif
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:51.905006+00:00
-- url     : https://prove2.me/theorems/92288c90-cd58-421b-901b-69375b99fdc5
-- title:
--   Pluri Taylor: taylor two unif
-- statement:
--   The Pluri Taylor construction uses the taylor two unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L88-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L88-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Set
variable {n : ℕ}

theorem GlobalTheory.PluriTaylor.taylor_two_unif (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∀ w ∈ closedBall (0 : V n) δ,
      φ (z + w) ≤ φ z + fderiv ℝ φ z w + (1 / 2) * fderiv ℝ (fderiv ℝ φ) z w w + η * ‖w‖ ^ 2 := by sorry
