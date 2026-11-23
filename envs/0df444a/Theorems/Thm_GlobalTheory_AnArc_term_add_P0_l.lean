-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_term_add_P0_l
-- name    : GlobalTheory.AnArc.term_add_P0_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:43.239084+00:00
-- url     : https://prove2.me/theorems/b944585c-6333-42f8-a7f2-cefe52925413
-- title:
--   An Arc: term add P0 l
-- statement:
--   The An Arc construction uses the term add P0 l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L613-L628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L613-L628

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

theorem GlobalTheory.AnArc.term_add_P0_l {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (μ : A.X) (l : A.abelian₂)
    (v : A.V) : A.term j α th μ (v + A.P0 (La.mk 0 0 l)) =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j * A.term j α th μ v := by sorry
