-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_tate_Pw
-- name    : GlobalTheory.AnArc.tate_Pw
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:56:03.797362+00:00
-- url     : https://prove2.me/theorems/1f69da28-e5df-4dbe-997c-b3d2e4fddef3
-- title:
--   An Arc: tate Pw
-- statement:
--   The An Arc construction uses the tate Pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L712-L716
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L712-L716

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

theorem GlobalTheory.AnArc.tate_Pw (τ₀ w : ℂ) (y : ℤ) (n : ℤ →+ ℤ) :
    ((tate τ₀).Pw w (La.mk (A := tate τ₀) y n 0)).1 (1 : ℤ) = n 1 + y * (τ₀ + 2 * w) := by sorry
