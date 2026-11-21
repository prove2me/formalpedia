-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isItoVersion
-- name    : LevyStochCalc.Brownian.Ito.exists_isItoVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:21:41.656659+00:00
-- url     : https://prove2.me/theorems/79392605-38e4-4b82-a309-00f35f8d3d51
-- title:
--   exists isItoVersion
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_isItoVersion` is extracted from `LevyStochCalc.Brownian.ItoVersionExists`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence of a continuous adapted version of an Itô process

The Itô integral has an a.e.-continuous modification by Kolmogorov–Chentsov. Zeroing its paths
on a null set makes them continuous everywhere, and the resulting process stays adapted when the
filtration contains the null sets. Adding a measurable initial value and the drift's
(Lipschitz, hence continuous) window integral gives an `IsItoVersion`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem` — a σ-algebra of the filtration
  containing the null sets does not distinguish a.e.-equal functions.
* `LevyStochCalc.Brownian.Ito.dyadicApprox` — the dyadic approximation from below, whose values
  lie in a countable set.
* `LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification` — the Itô integral has a
  continuous adapted modification.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.exists_isItoVersion
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable ℱ bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X := by sorry
