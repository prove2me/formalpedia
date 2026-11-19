-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_eLpNorm_exp_I_mul_sub
-- name    : LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:39:31.102245+00:00
-- url     : https://prove2.me/theorems/5dcdb202-734d-490d-bb31-d853274d1308
-- title:
--   tendsto eLpNorm exp I mul sub
-- statement:
--   The source theorem `LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub` is extracted from `LevyStochCalc.Probability.CharacterL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters of real variables in `L²`

For a real frequency `u` the character `x ↦ e^{iux}` has modulus one and is `|u|`-Lipschitz, and
`e^{iux} − 1` is bounded by `|u| |x|` and by two. So along `L²` convergence of real variables
`Y_n → Y` the characters `e^{iuY_n}` converge in `L²`, and a square-integrable `Y` gives a
square-integrable `e^{iuY} − 1` on any measure and a square-integrable `e^{iuY}` on a finite one.
The complex pairing `∫ F G` is the `L²` inner product of `F̄` and `G`, so it is continuous along
`L²` convergence in each argument.

## Main statements

* `LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two` — `‖e^{it} − 1‖ ≤ 2`.
* `LevyStochCalc.Probability.integrable_exp_I_mul_mul` — a character times an integrable
  variable is integrable.
* `LevyStochCalc.Probability.memLp_exp_I_mul`, `LevyStochCalc.Probability.memLp_exp_I_mul_sub_one`
  — square integrability of `e^{iuY}` and of `e^{iuY} − 1`.
* `LevyStochCalc.Probability.memLp_mul_of_norm_le` — a bounded multiple of a square-integrable
  variable is square integrable.
* `LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm` — continuity of the complex
  pairing along `L²` convergence.
* `LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_mul_sub_mul` — `L²` convergence passes to the complex
  embedding, to the characters and to bounded multiples.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

theorem _root_.LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m) atTop (𝓝 0) := by sorry
