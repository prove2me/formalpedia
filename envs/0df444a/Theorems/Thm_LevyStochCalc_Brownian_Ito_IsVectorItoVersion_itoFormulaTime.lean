-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormulaTime
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:04:49.372179+00:00
-- url     : https://prove2.me/theorems/666ac70f-25e1-43ff-8e19-4233becb0293
-- title:
--   itoFormulaTime
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime` is extracted from `LevyStochCalc.Brownian.VectorItoTimeFormula`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a time-dependent function of a vector Itô process

Applying the state-only formula to the process augmented by its own time separates the time
derivative — paired with the unit drift of the extra coordinate — from the space derivatives.
The extra coordinate carries no diffusion, so it contributes neither a stochastic integral nor a
quadratic-variation term.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime` — Itô's formula for a
  time-dependent function.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section TimeFormula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ q : Fin n, Measurable fun ω => X₀ ω q)
    (hbm : ∀ q, Measurable (Function.uncurry (bdrift q))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (q : Fin n) (ω : Ω) (s : ℝ), |bdrift q ω s| ≤ B)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin (n + 1) → ℝ) → ℝ} {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hfC : ContDiff ℝ 2 f)
    (hmg : ∀ (q : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s))
    (hpg : ∀ (q : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s)
    (hqg : ∀ (q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (timeAugProcess X T ω) - f (timeAugProcess X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' 0 (timeAugProcess X s ω) ∂volume)
        + (∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' q.succ (timeAugProcess X s ω) * bdrift q ω s ∂volume)
        + (∑ q : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s)
            (hmg q k) (hpg q k) (hqg q k) T ω)
        + 1 / 2 * ∑ q : Fin n, ∑ q' : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' q.succ q'.succ (timeAugProcess X s ω)
              * ∑ k : Fin d, H q k ω s * H q' k ω s ∂volume := by sorry
