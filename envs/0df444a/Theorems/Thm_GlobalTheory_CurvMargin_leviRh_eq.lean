-- Prove2me | Theorems.Thm_GlobalTheory_CurvMargin_leviRh_eq
-- name    : GlobalTheory.CurvMargin.leviRh_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:30:17.128777+00:00
-- url     : https://prove2.me/theorems/36be996c-7b5b-41e9-99d3-2b8ad5f2f3e1
-- title:
--   Curv Margin: levi Rh eq
-- statement:
--   The Curv Margin construction uses the levi Rh eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PhlaBlockWtCpt.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PhlaBlockWtCpt.lean#L48-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PhlaBlockWtCpt
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
open GlobalTheory GlobalTheory.CurvMargin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.CurvMargin.leviRh_eq {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    leviRh X x0 z ξ = leviM X (phla X (blockWt X)) x0 z ξ := by sorry
