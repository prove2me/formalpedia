-- Prove2me | Theorems.Thm_GlobalTheory_Unfold_unique_translate
-- name    : GlobalTheory.Unfold.unique_translate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:52.940012+00:00
-- url     : https://prove2.me/theorems/88cf82c7-b9e5-418f-a538-bb7078d38ff4
-- title:
--   Unfold: unique translate
-- statement:
--   The Unfold construction uses the unique translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L109-L126

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

theorem GlobalTheory.Unfold.unique_translate (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by sorry
