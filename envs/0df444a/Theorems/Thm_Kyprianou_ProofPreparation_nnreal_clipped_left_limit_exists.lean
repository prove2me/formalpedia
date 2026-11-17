-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_nnreal_clipped_left_limit_exists
-- name    : Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:07.750896+00:00
-- url     : https://prove2.me/theorems/996125a2-3322-4059-8d7b-97581b34d827
-- title:
--   Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem nnreal_clipped_left_limit_exists
    (f : ℝ → ℝ)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => f (min (v : ℝ) 1))
        (𝓝[<] u) (𝓝 l) := by sorry
end Kyprianou.ProofPreparation
