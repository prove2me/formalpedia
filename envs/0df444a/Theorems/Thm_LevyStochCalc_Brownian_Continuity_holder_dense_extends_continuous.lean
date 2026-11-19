-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_holder_dense_extends_continuous
-- name    : LevyStochCalc.Brownian.Continuity.holder_dense_extends_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:10:57.52621+00:00
-- url     : https://prove2.me/theorems/1ea7eeaf-4cab-4f31-82f9-afe2756cbb8d
-- title:
--   holder dense extends continuous
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Continuity.holder_dense_extends_continuous` is extracted from `LevyStochCalc.Brownian.ContinuityDyadicChaining`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Construction_F000
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

theorem _root_.LevyStochCalc.Brownian.Continuity.holder_dense_extends_continuous {α K δ₀ : ℝ}
    (hα : 0 < α) (_hK : 0 < K) (hδ₀ : 0 < δ₀)
    (D : Set ℝ) (h_dense : Dense D)
    (f : ℝ → ℝ)
    (h_holder_dyadic : ∀ s ∈ D, ∀ t ∈ D, |s - t| ≤ δ₀ →
      |f s - f t| ≤ K * |s - t| ^ α) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ s ∈ D, g s = f s := by sorry
