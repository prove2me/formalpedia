-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_exists_unique_solvesBSDEJ
-- name    : LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:21:04.747178+00:00
-- url     : https://prove2.me/theorems/abfadf42-1e51-4416-8456-986e48217118
-- title:
--   Existence and uniqueness of backward stochastic differential equations with jumps
-- statement:
--   Fix a Lévy driver with Brownian and Poisson components, an augmented joint filtration and a positive finite time horizon T. Assume the mark space has a countably generated σ-algebra and measurable singletons. Let the BSDE-with-jumps generator f be measurable in its arguments, uniformly Lipschitz in the value y, Brownian integrand z and jump integrand u, where the distance between jump integrands is the square root of their L²(ν) energy. Require square integrability of the generator at zero on the horizon and of the terminal random variable ξ, with ξ measurable in the augmented joint filtration at time T. The theorem asserts existence of a triple of processes (Y,Z,U) satisfying the original Lean SolvesBSDEJ predicate. If two solution triples satisfy that predicate, their value processes agree almost surely at each time in [0,T], while the Brownian integrands have zero squared-energy difference in every coordinate and the Poisson integrands have zero marked-energy difference. The result retains the exact source predicate, assumptions and time convention.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc/blob/main/LevyStochCalc/BSDEJ/ExistenceUniqueness.lean

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F002
import Definitions.Def_LevyStochCalc_BSDEJ_Uniqueness_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence and uniqueness for a backward equation with jumps over a Lévy driver

`exists_unique_solvesBSDEJ` combines the fixed point of the Picard scheme, `exists_solvesBSDEJ`,
with the uniqueness statements `SolvesBSDEJ.unique_Y_Icc`, `SolvesBSDEJ.unique_Z` and
`SolvesBSDEJ.unique_U`: a generator that is Lipschitz in `(y, z, u)` with the `L²(ν)` distance
in the jump variable and square integrable at the origin on the horizon, together with a square
integrable terminal datum measurable for the augmented joint filtration at the horizon, admits a
solution triple in `S² × H² × H²_ν` over the augmented joint filtration of the driver, and any
two solutions agree: the value processes almost surely at every time of the horizon, the
diffusion and jump integrands with vanishing energy of their difference on the horizon.

## Source

* Tang & Li, "Necessary conditions for optimal control of stochastic systems with random jumps",
  SICON 32(5), 1994, Theorem 3.1 (stated there for a generator reading a forward jump diffusion).
* Delong, "BSDEs with Jumps and their Actuarial and Financial Applications", Springer 2013,
  Theorem 4.1.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

theorem _root_.LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u : E → ℝ, Measurable fun r : ℝ × ℝ × (Fin d → ℝ) => f r.1 r.2.1 r.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
        SolvesBSDEJ D f ξ T Y Z U) ∧
      ∀ (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)) (U₁ U₂ : ℝ → Ω → E → ℝ),
        SolvesBSDEJ D f ξ T Y₁ Z₁ U₁ → SolvesBSDEJ D f ξ T Y₂ Z₂ U₂ →
          (∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t =ᵐ[P] Y₂ t) ∧
          (∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0) ∧
          Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 := by sorry
