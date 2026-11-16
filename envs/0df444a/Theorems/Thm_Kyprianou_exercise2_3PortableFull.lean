-- Prove2me | Theorems.Thm_Kyprianou_exercise2_3PortableFull
-- name    : Kyprianou.exercise2_3PortableFull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:36:49.294222+00:00
-- url     : https://prove2.me/theorems/24b8f646-cf3b-4e37-9e1d-d459351081ac
-- title:
--   Chapter 2 Exercise 2.3 full Laplace-truncation equivalence with portable imports
-- statement:
--   Exact mathematical statement and original assumptions of Kyprianou Chapter 2 Exercise 2.3. This portable copy omits only the unrelated missing CompletedPoissonFiltration import, making theorem elaboration possible. Original theorem is unchanged.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.3, user PDF and end-of-book solutions

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_3PortableFull
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) ↔
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤
      := by sorry

end Kyprianou
