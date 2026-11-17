-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_unit_discontinuity_has_nonzero_left_jump
-- name    : Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:04.561816+00:00
-- url     : https://prove2.me/theorems/b9e866b7-4f29-4cb7-8f52-ea87e7103c62
-- title:
--   Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem unit_discontinuity_has_nonzero_left_jump
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hdisc : ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t) :
    ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ f t ≠ l := by sorry
end Kyprianou.ProofPreparation
