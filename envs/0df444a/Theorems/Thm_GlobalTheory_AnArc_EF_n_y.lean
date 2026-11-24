-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_EF_n_y
-- name    : GlobalTheory.AnArc.EF_n_y
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:33.540516+00:00
-- url     : https://prove2.me/theorems/e96084e3-3b5f-424e-a498-d41377eb5a01
-- title:
--   An Arc: EF n y
-- statement:
--   The An Arc construction uses the EF n y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L441-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L441-L442

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

theorem GlobalTheory.AnArc.EF_n_y (n : A.X →+ ℤ) (y : A.X) : A.EF (La.mk 0 n 0) (La.mk y 0 0) = -n y := by sorry
