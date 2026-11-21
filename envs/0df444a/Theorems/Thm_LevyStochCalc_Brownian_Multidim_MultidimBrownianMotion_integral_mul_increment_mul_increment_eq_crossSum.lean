-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_increment_mul_increment_eq_crossSum
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:10:37.706483+00:00
-- url     : https://prove2.me/theorems/06933fcd-8677-460a-a69f-b936a5a61238
-- title:
--   integral mul increment mul increment eq crossSum
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum` is extracted from `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The direct cross identity for distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, the identity
`E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` holds for a bounded `ℱ_a`-measurable weight `Z`: along a
uniform grid of `[a, b]`, the product of the two increments telescopes into cell-wise terms, the
terms with a past factor are killed by conditioning, and the sum of the cell-wise cross products
has second moment `(b - a)² / m` by the independence of the two coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section DirectCross

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum (W : MultidimBrownianMotion P d)
    (i j : Fin d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z)
    (hZm : Measurable Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω)) ∂P
      = ∫ ω, Z ω * ∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω) ∂P := by sorry
