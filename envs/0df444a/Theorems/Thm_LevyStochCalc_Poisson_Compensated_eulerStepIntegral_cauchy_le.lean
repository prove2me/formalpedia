-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_eulerStepIntegral_cauchy_le
-- name    : LevyStochCalc.Poisson.Compensated.eulerStepIntegral_cauchy_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T10:28:48.341642+00:00
-- url     : https://prove2.me/theorems/d37a9853-32b2-46a0-9807-d514eeded6a2
-- title:
--   eulerStepIntegral cauchy le
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.eulerStepIntegral_cauchy_le` is extracted from `LevyStochCalc.Poisson.CompensatedDensityLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.eulerStepIntegral_cauchy_le
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) (φ
      : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤) {a b : ℕ} (hab : a ≤ b)
    {Kia : Fin (2 ^ a) → ℕ} {Kib : Fin (2 ^ b) → ℕ}
    (Bia : ∀ i, Fin (Kia i) → Set E) (Bib : ∀ i, Fin (Kib i) → Set E)
    (cia : ∀ i, Fin (Kia i) → Ω → ℝ) (cib : ∀ i, Fin (Kib i) → Ω → ℝ)
    (hBiam : ∀ i k, MeasurableSet (Bia i k)) (hBibm : ∀ i k, MeasurableSet (Bib i k))
    (hBiaS : ∀ i k, Bia i k ⊆ S) (hBibS : ∀ i k, Bib i k ⊆ S)
    (hciab : ∀ i k, ∃ M, ∀ ω, |cia i k ω| ≤ M) (hcibb : ∀ i k, ∃ M, ∀ ω, |cib i k ω| ≤ M)
    (hciam : ∀ i k, Measurable (cia i k)) (hcibm : ∀ i k, Measurable (cib i k))
    (hciaa : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T a i.castSucc)) (cia i k))
    (hciba : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T b i.castSucc)) (cib i k)) :
    ∫⁻ ω, (‖(∑ i : Fin (2 ^ a), ∑ k, cia i k ω
          * N.compensated (Set.Ioc (dyadicPartition T a i.castSucc)
              (dyadicPartition T a i.succ) ×ˢ Bia i k) ω)
        - ∑ i : Fin (2 ^ b), ∑ k, cib i k ω
          * N.compensated (Set.Ioc (dyadicPartition T b i.castSucc)
              (dyadicPartition T b i.succ) ×ˢ Bib i k) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e
            - ∑ i : Fin (2 ^ a), (Set.Ioc (dyadicPartition T a i.castSucc)
                (dyadicPartition T a i.succ)).indicator (fun _ => (1 : ℝ)) s
              * ∑ k, cia i k ω * (Bia i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
                ∂P)
        + 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e
            - ∑ i : Fin (2 ^ b), (Set.Ioc (dyadicPartition T b i.castSucc)
                (dyadicPartition T b i.succ)).indicator (fun _ => (1 : ℝ)) s
              * ∑ k, cib i k ω * (Bib i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
                ∂P) := by sorry
