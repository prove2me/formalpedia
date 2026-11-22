-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_wNorm_sub_le_two_mul_mid
-- name    : LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_two_mul_mid
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T07:58:53.093918+00:00
-- url     : https://prove2.me/theorems/22c938de-c48a-4cac-93f2-1e1cfe30c72f
-- title:
--   wNorm sub le two mul mid
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_two_mul_mid` is extracted from `LevyStochCalc.BSDEJ.PicardIteratesCauchy`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The geometric Cauchy estimate for the Picard iterates

The exponentially weighted norm `wNorm` at a nonnegative weight dominates the energies of the
value process, of the diffusion coordinates and of the jump integrand, and is subadditive along
an intermediate triple up to a factor of two. Combined with the one-step contraction at the Young
weight `β = max 2 (24 L²)`, this gives a geometric bound with ratio `1/4` on the weighted norm of
consecutive Picard iterates, and hence a Cauchy estimate for the iterates in the weighted norm
and in the unweighted energies on the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Subadditivity and lower bounds for the weighted norm -/

section WNorm

variable {β T : ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_two_mul_mid {Y₁ Y₂ Y₃ : ℝ → Ω → ℝ} {Z₁ Z₂ Z₃ : ℝ → Ω → (Fin d → ℝ)}
    {U₁ U₂ U₃ : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₃ t ω) (fun t ω => Z₁ t ω - Z₃ t ω)
        (fun t ω e => U₁ t ω e - U₃ t ω e)
      ≤ 2 * wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e)
        + 2 * wNorm P ν β T (fun t ω => Y₂ t ω - Y₃ t ω) (fun t ω => Z₂ t ω - Z₃ t ω)
            (fun t ω e => U₂ t ω e - U₃ t ω e) := by sorry
