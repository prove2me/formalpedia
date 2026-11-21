-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_window_norm_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:38:09.121462+00:00
-- url     : https://prove2.me/theorems/86132e1a-0401-4202-b7c9-4a343d4010af
-- title:
--   lintegral window norm sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le` is extracted from `LevyStochCalc.Brownian.VectorItoProcessWindow`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Window moments of a vector Itô process

Integrating the increment moments of a version of a vector Itô process over a time window gives
bounds on the joint integrals `∫∫_{(u,v]} 𝔼‖X_s − X_u‖ ds` and `∫∫_{(u,v]} 𝔼‖X_s − X_u‖² ds`,
which are what the Riemann-sum estimates consume.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le` — the `L¹` window
  bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_sq_norm_sub_le` — the `L²`
  window bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorWindow

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

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_window_norm_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal ‖X s ω - X u ω‖ ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u)
        * ((n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))))) := by sorry
