-- Prove2me | Theorems.Thm_GlobalTheory_KronOff_eq_of_mem_satBall
-- name    : GlobalTheory.KronOff.eq_of_mem_satBall
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:48.188894+00:00
-- url     : https://prove2.me/theorems/236e1ba1-b46c-426d-8641-90b599c0246c
-- title:
--   Kron Off: eq of mem sat Ball
-- statement:
--   The Kron Off construction uses the eq of mem sat Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableIndicatorOfContOn.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableIndicatorOfContOn.lean#L87-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.KronOff.eq_of_mem_satBall {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (δ : ℝ)
    (hδ : Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : x ∈ satBall X x0 δ) :
    ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b := by sorry
