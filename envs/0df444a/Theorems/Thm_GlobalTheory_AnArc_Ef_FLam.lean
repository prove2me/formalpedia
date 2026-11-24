-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Ef_FLam
-- name    : GlobalTheory.AnArc.Ef_FLam
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:42.199571+00:00
-- url     : https://prove2.me/theorems/96112932-973c-4973-b5f8-4823fff3a1da
-- title:
--   An Arc: Ef FLam
-- statement:
--   The An Arc construction uses the Ef FLam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L174-L177

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

theorem GlobalTheory.AnArc.Ef_FLam (a : O) (l m : A.abelian₂) : A.Ef (A.FLam a l) m = A.Ef l (A.FLam (star a) m) := by sorry
