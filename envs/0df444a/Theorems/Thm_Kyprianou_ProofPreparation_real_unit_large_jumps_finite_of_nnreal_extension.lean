-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_unit_large_jumps_finite_of_nnreal_extension
-- name    : Kyprianou.ProofPreparation.real_unit_large_jumps_finite_of_nnreal_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:07.442647+00:00
-- url     : https://prove2.me/theorems/d3c5ddae-bfa2-449e-997b-80593ed1aa17
-- title:
--   Kyprianou.ProofPreparation.real_unit_large_jumps_finite_of_nnreal_extension
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.real_unit_large_jumps_finite_of_nnreal_extension from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem real_unit_large_jumps_finite_of_nnreal_extension
    (f : ℝ → ℝ) (Y : ℝ≥0 → ℝ)
    (heq : ∀ u : ℝ≥0, u ≤ 1 → Y u = f (u : ℝ))
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Set.Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (c : ℝ) (hc : 0 < c) :
    Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ c < |f t - l|} := by sorry
end Kyprianou.ProofPreparation
