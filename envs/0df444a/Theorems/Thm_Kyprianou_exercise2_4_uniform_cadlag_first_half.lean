-- Prove2me | Theorems.Thm_Kyprianou_exercise2_4_uniform_cadlag_first_half
-- name    : Kyprianou.exercise2_4_uniform_cadlag_first_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:08.884168+00:00
-- url     : https://prove2.me/theorems/770098da-8886-4f12-932a-2ee0bd045bc1
-- title:
--   Kyprianou.exercise2_4_uniform_cadlag_first_half
-- statement:
--   Automatically extracted helper theorem Kyprianou.exercise2_4_uniform_cadlag_first_half from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
-- source:
--   candidate-decomposition:14556a83-e4b8-429a-a267-9d409e99daea:90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_4_uniform_cadlag_first_half :
    let isCadlagOnUnit : (ℝ → ℝ) → Prop := fun f =>
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc t 1) t) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ∃ a : ℝ, Tendsto f (nhdsWithin t (Set.Iio t)) (nhds a))
    ∀ (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ n, isCadlagOnUnit (fn n)) →
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ t ∈ Set.Icc (0 : ℝ) 1, |fn n t - f t| < ε) →
      isCadlagOnUnit f := by sorry
end Kyprianou
