-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_cross_increment_eq_zero_of_le
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:12:36.547273+00:00
-- url     : https://prove2.me/theorems/96fe862c-99ca-4804-8850-23d7d9ee0c1f
-- title:
--   integral cross increment eq zero of le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le` is extracted from `LevyStochCalc.Brownian.CrossOrthogonalityLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by sorry
