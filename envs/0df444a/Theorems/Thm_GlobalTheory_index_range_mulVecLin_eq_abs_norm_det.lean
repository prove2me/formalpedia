-- Prove2me | Theorems.Thm_GlobalTheory_index_range_mulVecLin_eq_abs_norm_det
-- name    : GlobalTheory.index_range_mulVecLin_eq_abs_norm_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:30.733256+00:00
-- url     : https://prove2.me/theorems/de891c17-6610-4994-b8c4-19515c6d5506
-- title:
--   Global Theory: index range mul Vec Lin eq abs norm det
-- statement:
--   The Global Theory construction uses the index range mul Vec Lin eq abs norm det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IndexRangeMulVecLinEqAbsNormDet.lean#L15-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IndexRangeMulVecLinEqAbsNormDet.lean#L15-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]

theorem GlobalTheory.index_range_mulVecLin_eq_abs_norm_det :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 E)), A.det ≠ 0 →
      (((LinearMap.range A.mulVecLin).toAddSubgroup.index : ℕ) : ℚ) =
        |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|) := by sorry
