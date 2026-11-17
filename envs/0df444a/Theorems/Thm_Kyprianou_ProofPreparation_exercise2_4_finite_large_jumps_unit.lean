-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_exercise2_4_finite_large_jumps_unit
-- name    : Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:05.56264+00:00
-- url     : https://prove2.me/theorems/68aaf574-ef4c-43d7-92b2-6cfeddb87510
-- title:
--   Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem exercise2_4_finite_large_jumps_unit
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ c : ℝ, 0 < c →
      Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧
          c < |f t - l|} := by sorry
end Kyprianou.ProofPreparation
