-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_PoissonRandomMeasure_exists_of_sigmaFinite
-- name    : LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:15:45.232212+00:00
-- url     : https://prove2.me/theorems/6fe5d1e3-d7b1-460b-b223-c25abebc7b47
-- title:
--   exists of sigmaFinite
-- statement:
--   The source theorem `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` is extracted from `LevyStochCalc.Poisson.RandomMeasure`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson random measure on `[0, ∞) × E`

A *Poisson random measure* on the time-space `[0, ∞) × E` (where `E` is a
measurable mark space with σ-finite intensity `ν`), defined over a
probability space `(Ω, P)`, is a measurable family

  `N : Ω → Measure (ℝ × E)`

with the following properties:

* For each measurable `B ⊆ ℝ × E` with `(volume.restrict [0,∞) ⊗ ν)(B) < ∞`,
  `N(·, B) ~ Poisson` with mean equal to that intensity.
* For any pairwise-disjoint family of such sets, the random variables
  `(N(·, B_i))_i` are independent under `P`.

This is the time-aware structure required for the *compensated* integral
`∫_0^t ∫_E φ(s, e) Ñ(ds, de)` to be well-defined.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009, §2.3, Thm 2.3.1.
* Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion Processes*,
  North-Holland 1989, §I.8.
* Sato, *Lévy Processes and Infinitely Divisible Distributions*,
  Cambridge 1999, §19.

## Construction

The intensity is `volume.restrict (Set.Ici 0) ⊗ ν` (Lebesgue restricted to `[0, ∞)` tensor `ν`
on the mark space). `PoissonRandomMeasure.exists_of_sigmaFinite` builds a Poisson random
measure by the Poisson recipe: the time-space is cut into the cells `[n, n+1) × sₘ` of a
σ-finite decomposition, each cell of positive intensity carries a Poisson number of
independent marks distributed according to the normalised intensity, and the cells are
superposed (`LevyStochCalc.Poisson.superposition`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (PoissonRandomMeasure P ν) := by sorry
