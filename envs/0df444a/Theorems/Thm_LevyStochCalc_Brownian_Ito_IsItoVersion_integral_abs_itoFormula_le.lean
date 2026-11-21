-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_integral_abs_itoFormula_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:00.726735+00:00
-- url     : https://prove2.me/theorems/334af710-8b61-4e3c-8304-953f6730c0ef
-- title:
--   integral abs itoFormula le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` is extracted from `LevyStochCalc.Brownian.ItoFormulaScalar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a scalar Itô process

For a continuous adapted version `X` of `X₀ + ∫ b ds + ∫ H dW` with bounded coefficients and
`f` twice differentiable with bounded derivatives and a Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. The proof telescopes the second-order Taylor expansion over a uniform grid and
bounds the four resulting errors, all of which vanish as the mesh does.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoGridError` — the `L¹` error of the grid approximation, as a
  function of the mesh.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` — that error bounds the
  `L¹` defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` — Itô's formula.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hX₀ : Measurable X₀) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {K₁ K₂ : ℝ} (hf'bd : ∀ x, |f' x| ≤ K₁) (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ x, |f'' x| ≤ K₂)
    {K : ℝ} (hK0 : 0 ≤ K) (hf''lip : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    (hmg : Measurable (Function.uncurry fun ω s => f' (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => f' (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖f' (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
          + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
            + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω
            + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
        ≤ itoGridError B C T K K₂ (T / (m : ℝ)) := by sorry
