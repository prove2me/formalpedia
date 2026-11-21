-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_lintegral_density_eq
-- name    : LevyStochCalc.BSDEJ.Solves.lintegral_density_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:22:26.409078+00:00
-- url     : https://prove2.me/theorems/ac9a4810-2d27-4976-88c9-01da0f08e44e
-- title:
--   lintegral density eq
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.lintegral_density_eq` is extracted from `LevyStochCalc.BSDEJ.PicardContractionNorm`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000

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

omit [SigmaFinite ν] in

theorem _root_.LevyStochCalc.BSDEJ.Solves.lintegral_density_eq [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P
      = Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by sorry
