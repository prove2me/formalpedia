-- Prove2me | Theorems.Thm_GlobalTheory_CurvMargin_tele_tail
-- name    : GlobalTheory.CurvMargin.tele_tail
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:54.769711+00:00
-- url     : https://prove2.me/theorems/c0840169-82fb-466e-a51d-3fe7c948d1ad
-- title:
--   Curv Margin: tele tail
-- statement:
--   The Curv Margin construction uses the tele tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PhlaBlockWtCpt.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PhlaBlockWtCpt.lean#L14-L24

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

theorem GlobalTheory.CurvMargin.tele_tail (L : ℕ → ℝ) (p : ℕ) : ∀ r : ℕ, p ≤ r →
    ∑ i ∈ Finset.range r, (if i < p then (0 : ℝ) else 1) * (L (i + 1) - L i) = L r - L p := by sorry
