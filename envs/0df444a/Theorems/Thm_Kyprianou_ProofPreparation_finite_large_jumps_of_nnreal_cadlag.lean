-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_large_jumps_of_nnreal_cadlag
-- name    : Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:05.720237+00:00
-- url     : https://prove2.me/theorems/1f73f0f7-a491-434e-af18-9adde0feaa4a
-- title:
--   Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem finite_large_jumps_of_nnreal_cadlag
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧
        δ < |Y u - l|}.Finite := by sorry
end Kyprianou.ProofPreparation
