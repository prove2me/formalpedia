-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_exists_jointIntegral_of_mean_zero
-- name    : LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_of_mean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:31:57.730758+00:00
-- url     : https://prove2.me/theorems/f7e5aa5f-6d92-40c3-a06c-2b22d7d48eeb
-- title:
--   exists jointIntegral of mean zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_of_mean_zero` is extracted from `LevyStochCalc.Driver.JointRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint range of a Lévy driver

The `L²` ranges of the `d` coordinate Itô integrals and of the compensated integral are pairwise
orthogonal and each closed, so their sum is closed and a square-integrable weight splits into a
part in the sum and a part orthogonal to it. The orthogonal part is a weight of mean zero,
measurable before the horizon, orthogonal to both ranges; when only the zero weight is such, the
weight is a joint integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Range

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

theorem _root_.LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_of_mean_zero (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P → (∫ ω, r ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
        ∫ ω, r ω * G.integral (D.W.W i) (hcoord i) ω ∂P = 0) →
      (∀ K : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * K.integral D.N hℱN ω ∂P = 0) →
      r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T),
      Z =ᵐ[P] jointIntegral hcoord hℱN G K := by sorry
