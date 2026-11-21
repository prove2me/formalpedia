-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion
-- name    : LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:37:14.778598+00:00
-- url     : https://prove2.me/theorems/6770f93f-95ca-4789-872b-023bc482db75
-- title:
--   exists isVectorItoVersion
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion` is extracted from `LevyStochCalc.Brownian.VectorItoVersionExists`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence of a continuous adapted version of a vector Itô process

Each entry of the diffusion matrix contributes an Itô integral against its own Brownian
coordinate, and each of those has a continuous adapted modification. Summing them over the
Brownian index and adding the initial value and the drift's window integral gives a continuous
adapted version of the vector Itô process.

## Main statements

* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Exists

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
  (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
  (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by sorry
