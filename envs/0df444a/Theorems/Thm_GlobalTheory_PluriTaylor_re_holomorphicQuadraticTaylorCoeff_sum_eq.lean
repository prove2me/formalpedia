-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_re_holomorphicQuadraticTaylorCoeff_sum_eq
-- name    : GlobalTheory.PluriTaylor.re_holomorphicQuadraticTaylorCoeff_sum_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:41.472989+00:00
-- url     : https://prove2.me/theorems/2e054bce-1410-409b-9f7f-5759c6432002
-- title:
--   Pluri Taylor: re holomorphic Quadratic Taylor Coeff sum eq
-- statement:
--   The Pluri Taylor construction uses the re holomorphic Quadratic Taylor Coeff sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L59-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L59-L76

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

theorem GlobalTheory.PluriTaylor.re_holomorphicQuadraticTaylorCoeff_sum_eq (B : V n →L[ℝ] V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    8 * (∑ j, ∑ k, ((a j : ℂ) + (c j : ℂ) * I) * ((a k : ℂ) + (c k : ℂ) * I) * qc B j k).re =
      B (∑ k, (a k • bas n k + c k • (I • bas n k))) (∑ k, (a k • bas n k + c k • (I • bas n k))) -
      B (∑ k, (a k • (I • bas n k) - c k • bas n k)) (∑ k, (a k • (I • bas n k) - c k • bas n k)) := by sorry
