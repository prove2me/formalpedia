-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_eq_self_of_ae_symmetric
-- name    : Malliavin.symmetrizeL_eq_self_of_ae_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:32.867652+00:00
-- url     : https://prove2.me/theorems/a5d22671-d8c1-5236-9e35-4b10be61cd67
-- title:
--   Malliavin: symmetrize L eq self of ae symmetric
-- statement:
--   An a.e.-symmetric `Lp` function is fixed by `symmetrizeL`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L351-L359
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L351-L359

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

theorem Malliavin.symmetrizeL_eq_self_of_ae_symmetric (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ))
    (hf : ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f) :
    symmetrizeL E (μ := μ) n p f = f := by sorry
