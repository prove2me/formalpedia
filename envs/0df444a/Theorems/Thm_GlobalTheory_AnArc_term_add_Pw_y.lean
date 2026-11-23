-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_term_add_Pw_y
-- name    : GlobalTheory.AnArc.term_add_Pw_y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:07.092387+00:00
-- url     : https://prove2.me/theorems/0494f90c-3514-4487-9645-252fce1f5485
-- title:
--   An Arc: term add Pw y
-- statement:
--   The An Arc construction uses the term add Pw y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L637-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L637-L654

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

theorem GlobalTheory.AnArc.term_add_Pw_y (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (μ y : A.X) (v : A.V) :
    (A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) ^ j *
        (A.term j α th μ (v + A.Pw w (La.mk y 0 0)) * eTwoPi (w * A.exponent j α μ)) =
      A.term j α th (μ + y) v * eTwoPi (w * A.exponent j α (μ + y)) := by sorry
