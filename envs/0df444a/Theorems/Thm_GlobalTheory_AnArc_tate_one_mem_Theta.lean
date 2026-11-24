-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_tate_one_mem_Theta
-- name    : GlobalTheory.AnArc.tate_one_mem_Theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:51.39373+00:00
-- url     : https://prove2.me/theorems/da1d5d97-5938-4a59-81e0-053447903948
-- title:
--   An Arc: tate one mem Theta
-- statement:
--   The An Arc construction uses the tate one mem Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L721-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L721-L725

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

theorem GlobalTheory.AnArc.tate_one_mem_Theta (τ₀ : ℂ) (j : ℕ) (α : (tate τ₀).X) :
    (1 : (Fin (tate τ₀).gB → ℂ) → ℂ) ∈ (tate τ₀).Theta j α := by sorry
