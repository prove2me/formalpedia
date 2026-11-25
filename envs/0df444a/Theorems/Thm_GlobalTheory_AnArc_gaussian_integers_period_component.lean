-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_gaussian_integers_period_component
-- name    : GlobalTheory.AnArc.gaussian_integers_period_component
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:04.741087+00:00
-- url     : https://prove2.me/theorems/eea63709-0ed0-5a3c-8789-b28d95cba082
-- title:
--   An Arc: gaussian integers period component
-- statement:
--   The An Arc construction uses the gaussian integers period component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L893-L897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L893-L897

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

theorem GlobalTheory.AnArc.gaussian_integers_period_component (c τ₀ : ℂ) :
    ((gaussInt c τ₀).P0 (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv 1))).1 (1 : ℤ) = -(c / (2 * Complex.I)) := by sorry
