-- Prove2me | Theorems.Thm_GlobalTheory_FlatChecks_cfwM_all_eta
-- name    : GlobalTheory.FlatChecks.cfwM_all_eta
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:20.341088+00:00
-- url     : https://prove2.me/theorems/d42b2c16-b2bb-5bc7-a824-68232cb3ed22
-- title:
--   Flat Checks: cfw M all eta
-- statement:
--   The Flat Checks construction uses the cfw M all eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L24-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FlatChecks.cfwM_all_eta (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 ≤ a)
    (η : ℝ) (hη : 0 < η) : ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by sorry
