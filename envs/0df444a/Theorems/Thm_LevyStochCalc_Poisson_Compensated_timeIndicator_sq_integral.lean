-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_timeIndicator_sq_integral
-- name    : LevyStochCalc.Poisson.Compensated.timeIndicator_sq_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:39:31.706382+00:00
-- url     : https://prove2.me/theorems/ab1c1ea5-2c1b-4250-b78c-140998e853ad
-- title:
--   timeIndicator sq integral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.timeIndicator_sq_integral` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.timeIndicator_sq_integral
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T) (f : Fin N₀ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * f i) ^ 2 ∂volume
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc) * (f i) ^ 2 := by sorry
