-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_lintegral_nnnorm_sq_brownian
-- name    : LevyStochCalc.Examples.Nonvacuity.lintegral_nnnorm_sq_brownian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:12:37.042649+00:00
-- url     : https://prove2.me/theorems/ab945d53-cd6a-43ae-9141-a788bf3571ad
-- title:
--   lintegral nnnorm sq brownian
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.lintegral_nnnorm_sq_brownian` is extracted from `NonvacuityDrivers`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_L2Isometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the drivers and of their stochastic integrals

The basic objects of the library carry the second moments prescribed by the classical theory,
and are therefore distinct from the trivial process, the zero measure and the zero integral.

## Main statements

* `lintegral_nnnorm_sq_brownian` — `𝔼‖W_t‖² = t`, and `brownian_not_ae_zero` — `W_t ≠ 0`
  almost surely for `t > 0`.
* `lintegral_count_box` — `𝔼[N((0, T] × A)] = T · ν A`, and `count_not_ae_zero`.
* `lintegral_sq_itoIntegral_one` — the Itô integral of the constant integrand `1` over `[0, T]`
  has second moment `T`, and `itoIntegral_one_not_ae_zero`.
* `lintegral_sq_itoLevyIntegral_indicator` — the Itô–Lévy integral of the mark indicator `1_A`
  over `[0, T]` has second moment `ν A · T`, and `itoLevyIntegral_indicator_not_ae_zero`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.2, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

universe u v

section BrownianValue

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Examples.Nonvacuity.lintegral_nnnorm_sq_brownian (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal t := by sorry
