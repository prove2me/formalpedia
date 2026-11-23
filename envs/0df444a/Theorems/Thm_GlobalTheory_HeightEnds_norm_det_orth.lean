-- Prove2me | Theorems.Thm_GlobalTheory_HeightEnds_norm_det_orth
-- name    : GlobalTheory.HeightEnds.norm_det_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:43.044735+00:00
-- url     : https://prove2.me/theorems/c27c5b00-59f4-4688-8f09-879c318ee004
-- title:
--   Height Ends: norm det orth
-- statement:
--   The Height Ends construction uses the norm det orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsPosLeLatticeHeightBotTop.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsPosLeLatticeHeightBotTop.lean#L25-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
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
open GlobalTheory GlobalTheory.HeightEnds
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HeightEnds.norm_det_orth {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by sorry
