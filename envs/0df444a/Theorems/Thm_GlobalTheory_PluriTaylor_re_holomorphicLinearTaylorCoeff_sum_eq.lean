-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_re_holomorphicLinearTaylorCoeff_sum_eq
-- name    : GlobalTheory.PluriTaylor.re_holomorphicLinearTaylorCoeff_sum_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:03:45.360445+00:00
-- url     : https://prove2.me/theorems/839660ba-3c26-4410-8a63-07a90d61b099
-- title:
--   Pluri Taylor: re holomorphic Linear Taylor Coeff sum eq
-- statement:
--   The Pluri Taylor construction uses the re holomorphic Linear Taylor Coeff sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L49-L57

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
open Complex Set
variable {n : ℕ}
noncomputable section

theorem GlobalTheory.PluriTaylor.re_holomorphicLinearTaylorCoeff_sum_eq (F : V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    2 * (∑ j, ((a j : ℂ) + (c j : ℂ) * I) * lc F j).re =
      F (∑ k, (a k • bas n k + c k • (I • bas n k))) := by sorry
