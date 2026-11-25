-- Prove2me | Theorems.Thm_GlobalTheory_ofReal_tsum_sq_le_tsum_div_mul_tsum
-- name    : GlobalTheory.ofReal_tsum_sq_le_tsum_div_mul_tsum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:54.866711+00:00
-- url     : https://prove2.me/theorems/b128f052-fea1-50f6-b59d-bfc316cd0293
-- title:
--   Global Theory: of Real tsum sq le tsum div mul tsum
-- statement:
--   The Global Theory construction uses the of Real tsum sq le tsum div mul tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealTsumSqLeTsumDivMulTsum.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealTsumSqLeTsumDivMulTsum.lean#L12-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealTsumSqLeTsumDivMulTsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ofReal_tsum_sq_le_tsum_div_mul_tsum {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by sorry
