-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_eq_self_iff
-- name    : Malliavin.symmetrizeL_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:22.585191+00:00
-- url     : https://prove2.me/theorems/c672b1e1-b83c-4ac0-a086-7fbce17104b4
-- title:
--   Malliavin: symmetrize L eq self iff
-- statement:
--   The fixed points of `symmetrizeL` are exactly the a.e.-symmetric functions.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L378-L382
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L378-L382

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}

theorem Malliavin.symmetrizeL_eq_self_iff (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p f = f ↔ ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f := by sorry
