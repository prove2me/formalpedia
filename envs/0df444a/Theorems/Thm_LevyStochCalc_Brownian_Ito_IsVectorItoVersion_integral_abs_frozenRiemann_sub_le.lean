-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_frozenRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:39:15.595929+00:00
-- url     : https://prove2.me/theorems/68db8f8c-7897-4b90-8619-008656d180a9
-- title:
--   integral abs frozenRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.VectorItoTimeRiemann`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Frozen-weight Riemann sums for a vector Itô process

Freezing a Lipschitz function of a continuous vector Itô process at the left endpoints of a
uniform grid and pairing it with the cell integrals of a bounded time density gives a Riemann sum
for `∫_0^T φ(X_s)·w_s ds`, with an `L¹` error of order `√(T/m)`. Both the process's own drift
coordinates and the entries of the diffusion matrix are admissible densities.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le` — the `L¹`
  error of a frozen-weight Riemann sum along a vector Itô process.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorRiemann

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
        ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by sorry
