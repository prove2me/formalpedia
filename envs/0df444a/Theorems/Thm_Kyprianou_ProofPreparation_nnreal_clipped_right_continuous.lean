-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_nnreal_clipped_right_continuous
-- name    : Kyprianou.ProofPreparation.nnreal_clipped_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:03.554729+00:00
-- url     : https://prove2.me/theorems/a514a493-7e1f-4154-9684-8b7eb71c2b84
-- title:
--   Kyprianou.ProofPreparation.nnreal_clipped_right_continuous
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.nnreal_clipped_right_continuous from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem nnreal_clipped_right_continuous
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => f (min (v : ℝ) 1)) (Set.Ici u) u := by sorry
end Kyprianou.ProofPreparation
