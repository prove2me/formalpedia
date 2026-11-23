-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_mul_mem_Theta
-- name    : GlobalTheory.AnArc.mul_mem_Theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:05.493503+00:00
-- url     : https://prove2.me/theorems/c0bcf7a9-ebf2-4468-a05f-a13ae97bd541
-- title:
--   An Arc: mul mem Theta
-- statement:
--   The An Arc construction uses the mul mem Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L484-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L484-L487

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

theorem GlobalTheory.AnArc.mul_mem_Theta {j j' : ℕ} {α α' : A.X} {th th' : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α)
    (h' : th' ∈ A.Theta j' α') : th * th' ∈ A.Theta (j + j') (α + α') := by sorry
