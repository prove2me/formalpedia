-- Prove2me | Theorems.Thm_Malliavin_ae_symmetric_of_symmetrizeL_eq_self
-- name    : Malliavin.ae_symmetric_of_symmetrizeL_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:36.660548+00:00
-- url     : https://prove2.me/theorems/b2d3cfaf-9584-5876-b04e-c432d745a0f8
-- title:
--   Malliavin: ae symmetric of symmetrize L eq self
-- statement:
--   Conversely, a fixed point of `symmetrizeL` is a.e.-symmetric.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L362-L375
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L362-L375

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

theorem Malliavin.ae_symmetric_of_symmetrizeL_eq_self (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) (hf : symmetrizeL E (μ := μ) n p f = f)
    (σ : Equiv.Perm (Fin n)) :
    (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f := by sorry
