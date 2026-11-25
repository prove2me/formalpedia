-- Prove2me | Theorems.Thm_GlobalTheory_FrameSplit_frameSplit
-- name    : GlobalTheory.FrameSplit.frameSplit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:20.884821+00:00
-- url     : https://prove2.me/theorems/8055d0ac-a3c0-4ff3-9f64-cd923acb84ef
-- title:
--   Frame Split: frame Split
-- statement:
--   The Frame Split construction uses the frame Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeOfSection.lean#L50-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralLeOfSection.lean#L50-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeOfSection
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
open GlobalTheory GlobalTheory.FrameSplit
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FrameSplit.frameSplit : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by sorry
