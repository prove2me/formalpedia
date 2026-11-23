-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_degeneratingTori_periodMap_eq_base_of_y_eq_zero
-- name    : GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:35.676263+00:00
-- url     : https://prove2.me/theorems/550697fe-caf0-40bd-bfb1-e5a98cfc5b0b
-- title:
--   An Arc: degenerating Tori period Map eq base of y eq zero
-- statement:
--   The An Arc construction uses the degenerating Tori period Map eq base of y eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L407-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L407-L408

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

theorem GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero (w : ℂ) {v : A.La} (hv : v.y = 0) : A.Pw w v = A.P0 v := by sorry
