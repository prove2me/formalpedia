-- Prove2me | Theorems.Thm_GlobalTheory_exists_common_integral_refinement
-- name    : GlobalTheory.exists_common_integral_refinement
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:04.994489+00:00
-- url     : https://prove2.me/theorems/fffc48b8-070d-4c5e-a04b-4827155b8abe
-- title:
--   Global Theory: exists common integral refinement
-- statement:
--   The Global Theory construction uses the exists common integral refinement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetDivIndexEqOfSpanEq.lean#L12-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetDivIndexEqOfSpanEq.lean#L12-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetDivIndexEqOfSpanEq
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
open GlobalTheory
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.exists_common_integral_refinement {V ι : Type} [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (w w' : ι → V) (hw' : LinearIndependent E w')
    (h : Submodule.span E (Set.range w) = Submodule.span E (Set.range w')) :
    ∃ A A' : Matrix ι ι (𝓞 E), A.det ≠ 0 ∧ A'.det ≠ 0 ∧
      (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) = (fun a => ∑ b, ((A' b a : 𝓞 E) : E) • w' b) := by sorry
