-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_degeneratingTori_basePeriodMap_smul
-- name    : GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:48.332662+00:00
-- url     : https://prove2.me/theorems/3cc8ccbc-682d-4e19-8cc6-b344e3211fbd
-- title:
--   An Arc: degenerating Tori base Period Map smul
-- statement:
--   The An Arc construction uses the degenerating Tori base Period Map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L410-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L410-L413

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

theorem GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul (a : O) (v : A.La) : A.P0 (a • v) = A.actV a (A.P0 v) := by sorry
