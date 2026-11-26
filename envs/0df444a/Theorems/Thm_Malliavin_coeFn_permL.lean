-- Prove2me | Theorems.Thm_Malliavin_coeFn_permL
-- name    : Malliavin.coeFn_permL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:56.023988+00:00
-- url     : https://prove2.me/theorems/76fbad4c-0e08-4277-a55f-28b580c00ff6
-- title:
--   Malliavin: coe Fn perm L
-- statement:
--   The Malliavin construction uses the coe Fn perm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L278-L282
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L278-L282

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

theorem Malliavin.coeFn_permL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n))
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ⇑(permL E (μ := μ) n p σ f) =ᵐ[Measure.pi fun _ : Fin n => μ]
      ⇑f ∘ fun t : Fin n → T => t ∘ σ := by sorry
