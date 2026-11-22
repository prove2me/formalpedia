-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_exists_admissible_wNorm_limit
-- name    : LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:15:48.97847+00:00
-- url     : https://prove2.me/theorems/48a617af-e233-416f-a9e3-9a6eec805856
-- title:
--   exists admissible wNorm limit
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` is extracted from `LevyStochCalc.BSDEJ.PicardLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F001

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

/-! ### Changing the input triple of a Picard step on a null set -/

/-! ### Triples at zero weighted distance -/

/-! ### The weighted norm against the energies -/

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

theorem _root_.LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit {q : ℕ → Triple Ω E d}
    (hA : ∀ n, Admissible D T (q n).1 (q n).2.1 (q n).2.2)
    (hcY : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).1 s ω - (q n).1 s ω) < ε)
    (hcZ : ∀ i : Fin d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).2.1 s ω i - (q n).2.1 s ω i) < ε)
    (hcU : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (q m).2.2 s ω e - (q n).2.2 s ω e) < ε)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      Admissible D T Y Z U ∧ Tendsto (fun n => wNorm P ν β T
        (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
        (fun t ω e => (q n).2.2 t ω e - U t ω e)) atTop (𝓝 0) := by sorry
