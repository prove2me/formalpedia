-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_exists_jointIntegral_augFiltration_of_isEmpty
-- name    : LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_isEmpty
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:48:00.408693+00:00
-- url     : https://prove2.me/theorems/278a1609-7430-423e-868b-7f8e6511a403
-- title:
--   exists jointIntegral augFiltration of isEmpty
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_isEmpty` is extracted from `LevyStochCalc.Driver.JointPRPDegenerate`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degenerate cases of the joint representation

Without Brownian coordinates the joint filtration is the Poisson one and the representation is
the compensated integral alone; without marks the Poisson random measure carries no information
and the representation is the Brownian one alone. Splitting on the two cases removes the
implementation hypotheses `0 < d` and `Nonempty E` from the representation theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Trivial

end Trivial

section Degenerate

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_isEmpty [IsEmpty E] (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by sorry
