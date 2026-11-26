-- Prove2me | Theorems.Thm_Malliavin_eLpNorm_symmetrize_le
-- name    : Malliavin.eLpNorm_symmetrize_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:55:29.615968+00:00
-- url     : https://prove2.me/theorems/ecbcc0ae-8f49-5183-9292-dc94ca7c45ee
-- title:
--   Malliavin: e Lp Norm symmetrize le
-- statement:
--   Symmetrization is an `Lᵖ`-contraction: `‖f̃‖_p ≤ ‖f‖_p` for `1 ≤ p`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L212-L233
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L212-L233

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

theorem Malliavin.eLpNorm_symmetrize_le {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) ≤
      eLpNorm f p (Measure.pi fun _ : Fin n => μ) := by sorry
