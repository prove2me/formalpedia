-- Prove2me | Theorems.Thm_GlobalTheory_FlatChecks_one_le_tt_iff
-- name    : GlobalTheory.FlatChecks.one_le_tt_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:26.920301+00:00
-- url     : https://prove2.me/theorems/e6c4b9a3-9c47-56e4-a632-55b0a6b32ade
-- title:
--   Flat Checks: one le tt iff
-- statement:
--   The Flat Checks construction uses the one le tt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/CoordDifferentiableAt.lean#L10-L22

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

theorem GlobalTheory.FlatChecks.one_le_tt_iff (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    1 ≤ X.tt ξ x τ ↔ 0 < X.c τ * X.maj x τ (Data.emb τ.1 ξ) ∧ X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1 := by sorry
