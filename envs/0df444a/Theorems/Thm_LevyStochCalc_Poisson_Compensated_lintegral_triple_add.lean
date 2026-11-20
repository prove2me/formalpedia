-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_lintegral_triple_add
-- name    : LevyStochCalc.Poisson.Compensated.lintegral_triple_add
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:46:13.474948+00:00
-- url     : https://prove2.me/theorems/43f6d6c9-e92a-46e1-b8d8-89c6ed3fea9f
-- title:
--   lintegral triple add
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.lintegral_triple_add` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkApprox`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.lintegral_triple_add
    {P : Measure Ω} {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    {u v : Ω → ℝ → E → ℝ≥0∞}
    (hu : Measurable (fun p : Ω × ℝ × E => u p.1 p.2.1 p.2.2)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (u ω s e + v ω s e) ∂ν ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, v ω s e ∂ν ∂volume ∂P := by sorry
