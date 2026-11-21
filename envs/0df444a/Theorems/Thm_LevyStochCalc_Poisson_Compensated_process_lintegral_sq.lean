-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_process_lintegral_sq
-- name    : LevyStochCalc.Poisson.Compensated.process_lintegral_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:13:22.9315+00:00
-- url     : https://prove2.me/theorems/12a8809d-e0a8-4a97-9732-b26d4a641815
-- title:
--   process lintegral sq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.process_lintegral_sq` is extracted from `LevyStochCalc.Poisson.CompensatedProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

end Process

section Isometry

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.process_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = horizonInt (P := P) (ν := ν) φ t := by sorry
