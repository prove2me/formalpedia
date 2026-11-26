-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_apply
-- name    : Malliavin.symmetrizeL_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:01.060879+00:00
-- url     : https://prove2.me/theorems/c4594da7-e537-4e77-a49e-958c38a66340
-- title:
--   Malliavin: symmetrize L apply
-- statement:
--   The Malliavin construction uses the symmetrize L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L295-L299
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L295-L299

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

theorem Malliavin.symmetrizeL_apply (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ f := by sorry
