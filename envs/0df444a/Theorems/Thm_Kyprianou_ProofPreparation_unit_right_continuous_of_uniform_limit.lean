-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_unit_right_continuous_of_uniform_limit
-- name    : Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:05.711306+00:00
-- url     : https://prove2.me/theorems/3f9af260-6369-4f66-9f9d-3b72f3d09de9
-- title:
--   Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.unit_right_continuous_of_uniform_limit from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
-- source:
--   candidate-decomposition:14556a83-e4b8-429a-a267-9d409e99daea:90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem unit_right_continuous_of_uniform_limit
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt (fn n) (Set.Icc t 1) t)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |fn n y - f y| < ε) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t := by sorry
end Kyprianou.ProofPreparation
