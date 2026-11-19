-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_map_finsetSum_gaussianReal
-- name    : LevyStochCalc.Probability.map_finsetSum_gaussianReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:29:17.161207+00:00
-- url     : https://prove2.me/theorems/b57d8601-0ec5-43c6-bfb6-7dc34ff2d146
-- title:
--   Independent centred Gaussian sums have additive variances
-- statement:
--   Let X be a family of measurable, mutually independent real random variables on a probability space P. Assume each coordinate $X_i$ has centred Gaussian law of variance $v_i$, where $v_i$ is nonnegative. For any finite index set s, the law of the finite random sum $\sum_{i\in s}$ $X_i$ is centred Gaussian with variance $\sum_{i\in s}$ $v_i$. This preserves the original source statement and its independent-coordinate assumptions.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc/blob/main/LevyStochCalc/Probability/GaussianSum.lean

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A finite sum of independent centred Gaussians

Adding one summand at a time, using that the sum of two independent Gaussians is Gaussian with
the sum of the variances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Probability.map_finsetSum_gaussianReal {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {v : ι → ℝ≥0}
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by sorry
