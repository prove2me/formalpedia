-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_exists_tendsto_of_uniform_approx
-- name    : Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:06.152733+00:00
-- url     : https://prove2.me/theorems/bd7b9040-f605-4005-ba56-bd027c874e17
-- title:
--   Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem exists_tendsto_of_uniform_approx
    {α : Type} (L : Filter α) [L.NeBot]
    (s : Set α) (hs : s ∈ L)
    (fn : ℕ → α → ℝ) (f : α → ℝ)
    (hfn : ∀ n, ∃ a : ℝ, Tendsto (fn n) L (𝓝 a))
    (huni : ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ∃ a : ℝ, Tendsto f L (𝓝 a) := by sorry
end Kyprianou.ProofPreparation
