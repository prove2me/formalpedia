-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_compensator_stronglyMeasurable
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.compensator_stronglyMeasurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:38:38.979689+00:00
-- url     : https://prove2.me/theorems/97a6a10a-2fea-463d-9247-6273b728b830
-- title:
--   compensator stronglyMeasurable
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.compensator_stronglyMeasurable` is extracted from `LevyStochCalc.Poisson.CompensatedQuadVar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.compensator_stronglyMeasurable (hG : G.Adapted ℱ) (t : ℝ) :
    @StronglyMeasurable Ω ℝ _ (ℱ t) (G.compensator t) := by sorry
