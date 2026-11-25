-- Prove2me | Theorems.Thm_GlobalTheory_PairUnfold_pairUnfold_of_unfold
-- name    : GlobalTheory.PairUnfold.pairUnfold_of_unfold
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:09.842031+00:00
-- url     : https://prove2.me/theorems/b5524440-4716-4f9c-8590-01390106ed2e
-- title:
--   Pair Unfold: pair Unfold of unfold
-- statement:
--   The Pair Unfold construction uses the pair Unfold of unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PairUnfoldOfUnfold.lean#L81-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PairUnfoldOfUnfold.lean#L81-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PairUnfoldOfUnfold
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
open GlobalTheory GlobalTheory.PairUnfold
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PairUnfold.pairUnfold_of_unfold :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (KaUnfoldStatement (E := E)) → (PairUnfoldStatement (E := E)) := by sorry
