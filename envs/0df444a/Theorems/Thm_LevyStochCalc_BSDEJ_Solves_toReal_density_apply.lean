-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_toReal_density_apply
-- name    : LevyStochCalc.BSDEJ.Solves.toReal_density_apply
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:27:38.955301+00:00
-- url     : https://prove2.me/theorems/5b18c4e4-7136-42ab-97fe-36e08cbef3b7
-- title:
--   toReal density apply
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.toReal_density_apply` is extracted from `LevyStochCalc.BSDEJ.PicardContractionNorm`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

variable [SigmaFinite ν]

omit [MeasurableSpace Ω] [SigmaFinite ν] in

theorem _root_.LevyStochCalc.BSDEJ.Solves.toReal_density_apply {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    {ω : Ω} {s : ℝ} (hU : ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    (density ν Y Z U ω s).toReal
      = (Y s ω) ^ 2 + (∑ j, (Z s ω j) ^ 2) + (∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by sorry
