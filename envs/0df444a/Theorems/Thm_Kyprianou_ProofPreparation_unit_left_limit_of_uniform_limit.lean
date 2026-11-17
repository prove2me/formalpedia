-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_unit_left_limit_of_uniform_limit
-- name    : Kyprianou.ProofPreparation.unit_left_limit_of_uniform_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:04.879704+00:00
-- url     : https://prove2.me/theorems/db3a3146-ce4e-421d-9145-e3cf804eb088
-- title:
--   Kyprianou.ProofPreparation.unit_left_limit_of_uniform_limit
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.unit_left_limit_of_uniform_limit from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem unit_left_limit_of_uniform_limit
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ a : ℝ, Tendsto (fn n) (𝓝[<] t) (𝓝 a))
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |fn n t - f t| < ε) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ a : ℝ, Tendsto f (𝓝[<] t) (𝓝 a) := by sorry
end Kyprianou.ProofPreparation
