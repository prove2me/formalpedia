-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_perFactor_ne_zero
-- name    : GlobalTheory.AnArc.perFactor_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:57:10.333807+00:00
-- url     : https://prove2.me/theorems/2a8e4b4a-45b3-4dc7-9f60-13694aae8dd4
-- title:
--   An Arc: per Factor ne zero
-- statement:
--   The An Arc construction uses the per Factor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean#L19-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
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
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.perFactor_ne_zero (w : ℂ) (la : A.La) (v : A.V) : A.perFactor w la v ≠ 0 := by sorry
