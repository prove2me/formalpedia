-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_tate_Sum
-- name    : GlobalTheory.AnArc.tate_Sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:34.037302+00:00
-- url     : https://prove2.me/theorems/fa675923-746e-46f9-a444-c2058e3de089
-- title:
--   An Arc: tate Sum
-- statement:
--   The An Arc construction uses the tate Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L731-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L731-L742

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.tate_Sum (τ₀ w : ℂ) (v : (tate τ₀).V) : (tate τ₀).Sum 1 (0 : ℤ) 1 w v =
    ∑' μ : ℤ, eTwoPi (μ ^ 2 * (τ₀ + 2 * w) / 2 + μ * v.1 (1 : ℤ)) := by sorry
