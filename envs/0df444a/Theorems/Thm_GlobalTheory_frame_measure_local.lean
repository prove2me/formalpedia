-- Prove2me | Theorems.Thm_GlobalTheory_frame_measure_local
-- name    : GlobalTheory.frame_measure_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:47:59.5758+00:00
-- url     : https://prove2.me/theorems/998cb4d3-afd0-5531-a0f6-0e754c2a95a3
-- title:
--   Global Theory: frame measure local
-- statement:
--   The Global Theory construction uses the frame measure local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralImageLeConst.lean#L119-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralImageLeConst.lean#L119-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralImageLeConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.FrameLoc
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.frame_measure_local :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) → (∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r, ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) → ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) := by sorry
