-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_quadVarRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:41:58.648429+00:00
-- url     : https://prove2.me/theorems/13d8b642-58c2-4ced-9dca-1f073500109c
-- title:
--   integral abs quadVarRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Decomposition and convergence of the quadratic-variation Riemann sum

The product of the increments of two coordinates of a continuous vector Itô process splits into a
drift–drift term, two drift–martingale terms and the product of the increments of the martingale
parts, and the last splits further into the compensated products on the diagonal in the Brownian
index, their compensators, and the cross terms off that diagonal. Weighting the products by a
bounded continuous function of the process frozen at the left endpoint of each cell of a uniform
grid, the five error terms are `O(m^{-1/2})` in `L¹` and the sixth group is a frozen-weight
Riemann sum for `∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`, so the weighted Riemann sum converges
in `L¹` to that integral at rate `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.prod_sub_ae` — the product of the increments of
  two coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae` — the decomposition of
  the weighted product sum into six groups.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` — the `L¹`
  rate of convergence of the weighted quadratic-variation Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorQuadVar

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

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + (Mφ * ((d : ℝ) * C ^ 2) * T
          + L * ((d : ℝ) * C ^ 2)
            * (T * ((n : ℝ) * (B * (T / (m : ℝ))
              + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by sorry
