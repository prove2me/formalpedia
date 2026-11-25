-- Prove2me | Theorems.Thm_GlobalTheory_MajNear_maj_near_orth
-- name    : GlobalTheory.MajNear.maj_near_orth
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:42.546855+00:00
-- url     : https://prove2.me/theorems/8fdef402-fd21-41a6-b72f-783c9edbceb5
-- title:
--   Maj Near: maj near orth
-- statement:
--   The Maj Near construction uses the maj near orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L69-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L69-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsomOfGramEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MajNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajNear.maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by sorry
