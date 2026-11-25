-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_gaussInt_EF
-- name    : GlobalTheory.AnArc.gaussInt_EF
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:46.652795+00:00
-- url     : https://prove2.me/theorems/66907b5d-d23f-4377-b3d0-892c207c4be9
-- title:
--   An Arc: gauss Int EF
-- statement:
--   The An Arc construction uses the gauss Int EF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L887-L891
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L887-L891

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

theorem GlobalTheory.AnArc.gaussInt_EF (c τ₀ : ℂ) : (gaussInt c τ₀).EF (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv 1))
    (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv ⟨0, 1⟩)) = -1 := by sorry
