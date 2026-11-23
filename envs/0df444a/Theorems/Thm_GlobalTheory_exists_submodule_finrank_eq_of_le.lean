-- Prove2me | Theorems.Thm_GlobalTheory_exists_submodule_finrank_eq_of_le
-- name    : GlobalTheory.exists_submodule_finrank_eq_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:14.899532+00:00
-- url     : https://prove2.me/theorems/98683af7-6ce4-46e8-b041-fbcc93566e25
-- title:
--   Global Theory: exists submodule finrank eq of le
-- statement:
--   The Global Theory construction uses the exists submodule finrank eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIsLUBHeightRpowLowerSemicontinuousOn.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIsLUBHeightRpowLowerSemicontinuousOn.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightContinuousOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
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

theorem GlobalTheory.exists_submodule_finrank_eq_of_le {K : Type} [Field K] {r i : ℕ} (h : i ≤ r) :
    ∃ W : Submodule K (Fin r → K), Module.finrank K W = i := by sorry
