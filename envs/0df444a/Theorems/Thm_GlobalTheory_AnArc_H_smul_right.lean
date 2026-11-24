-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_H_smul_right
-- name    : GlobalTheory.AnArc.H_smul_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:57:07.326946+00:00
-- url     : https://prove2.me/theorems/3c1c0a28-6999-4214-b594-d00d87d751b7
-- title:
--   An Arc: H smul right
-- statement:
--   The An Arc construction uses the H smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L119-L120

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

theorem GlobalTheory.AnArc.H_smul_right (c : ℂ) (z w : Fin A.gB → ℂ) : A.H z (c • w) = starRingEnd ℂ c * A.H z w := by sorry
