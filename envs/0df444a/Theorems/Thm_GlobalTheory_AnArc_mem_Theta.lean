-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_mem_Theta
-- name    : GlobalTheory.AnArc.mem_Theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:54.925004+00:00
-- url     : https://prove2.me/theorems/780bdd29-1c0d-4552-b23e-621208f1cd0d
-- title:
--   An Arc: mem Theta
-- statement:
--   The An Arc construction uses the mem Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L479-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/DegeneratingToriPeriodMapEqBaseOfYEqZero.lean#L479-L482

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

theorem GlobalTheory.AnArc.mem_Theta {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} : th ∈ A.Theta j α ↔
    Differentiable ℂ th ∧ ∀ (l : A.abelian₂) z, th (z + l) =
      (A.chi l * Complex.exp (Real.pi * A.H z l + Real.pi / 2 * A.H l l)) ^ j *
        Complex.exp (Real.pi * A.H (A.ct α) l) * th z := by sorry
