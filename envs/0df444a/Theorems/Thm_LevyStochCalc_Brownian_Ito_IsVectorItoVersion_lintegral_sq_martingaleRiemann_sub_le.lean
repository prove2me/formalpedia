-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_sq_martingaleRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:38:16.41368+00:00
-- url     : https://prove2.me/theorems/23caf2d5-9775-44d0-9911-4db459a22f38
-- title:
--   lintegral sq martingaleRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.VectorItoMartingaleRiemann`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoMartingaleRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale Riemann sum along a vector Itô process

Freezing a Lipschitz function of a continuous vector Itô process at the left endpoints of a
uniform grid and pairing it with the increments of an Itô integral against one Brownian
coordinate gives a Riemann sum for `∫_0^T φ(X_s)·G_s dWᵏ_s`, with an `L²` error of order
`√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the
  `L²` error of the martingale Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorFrozen

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

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
    (hGp : Probability.ProgressivelyMeasurable ℱ G)
    (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by sorry
