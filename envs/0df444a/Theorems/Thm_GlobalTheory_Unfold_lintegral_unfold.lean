-- Prove2me | Theorems.Thm_GlobalTheory_Unfold_lintegral_unfold
-- name    : GlobalTheory.Unfold.lintegral_unfold
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:46.468262+00:00
-- url     : https://prove2.me/theorems/1ac81fb0-3153-4c41-a18f-e6c6154eb0aa
-- title:
--   Unfold: lintegral unfold
-- statement:
--   The Unfold construction uses the lintegral unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L128-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L128-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
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
open GlobalTheory GlobalTheory.Unfold
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Unfold.lintegral_unfold (hM : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (ho : IsOrth X x0) (FF : Set (V (nd X))) (hF : IsFundSet X x0 FF) (ψ : Frame X.Ψ r → ℝ≥0∞)
    (hψ : Measurable ψ) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by sorry
