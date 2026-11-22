-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_exists_progressive_energy_limit_of_window
-- name    : LevyStochCalc.BSDEJ.Solves.exists_progressive_energy_limit_of_window
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:16:24.945091+00:00
-- url     : https://prove2.me/theorems/3813cd7a-77da-437f-8872-563ea64b1702
-- title:
--   exists progressive energy limit of window
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.exists_progressive_energy_limit_of_window` is extracted from `LevyStochCalc.BSDEJ.PicardLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.BSDEJ.Solves.exists_progressive_energy_limit_of_window (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} {H : ℕ → Ω → ℝ → ℝ} (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hfin : ∀ n, Brownian.Ito.energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s))
          atTop (𝓝 0) := by sorry
