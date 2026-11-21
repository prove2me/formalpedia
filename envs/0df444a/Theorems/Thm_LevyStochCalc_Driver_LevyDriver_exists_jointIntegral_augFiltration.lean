-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_exists_jointIntegral_augFiltration
-- name    : LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:38:01.923169+00:00
-- url     : https://prove2.me/theorems/c737bba6-3ed2-4bad-b2df-556bf09b2a8d
-- title:
--   exists jointIntegral augFiltration
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration` is extracted from `LevyStochCalc.Driver.JointPRP`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPerpBridge_F000
import Definitions.Def_LevyStochCalc_Driver_JointComplement_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation property of a Lévy driver

Over the augmented joint filtration, a square-integrable weight of mean zero that is measurable
before the horizon is the sum of Itô integrals against the Brownian coordinates and a compensated
integral against the Poisson random measure: the joint range is closed, the orthogonal remainder
is a weight of the same kind orthogonal to both ranges, and such a weight vanishes.
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

theorem _root_.LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration [Nonempty E] (D : LevyDriver.{u, v, w} P d ν)
    (hd : 0 < d) {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by sorry
