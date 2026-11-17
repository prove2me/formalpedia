-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_continuousWithinAt_of_uniform_approx
-- name    : Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:03.73751+00:00
-- url     : https://prove2.me/theorems/f51f75ad-ac93-44e6-8b9e-53852bf9b8a7
-- title:
--   Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.continuousWithinAt_of_uniform_approx from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem continuousWithinAt_of_uniform_approx
    {s : Set ℝ} {x : ℝ} (hx : x ∈ s)
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, ContinuousWithinAt (fn n) s x)
    (huni : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ContinuousWithinAt f s x := by sorry
end Kyprianou.ProofPreparation
