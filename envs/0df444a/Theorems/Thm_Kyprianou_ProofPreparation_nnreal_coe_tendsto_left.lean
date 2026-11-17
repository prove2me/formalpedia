-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_nnreal_coe_tendsto_left
-- name    : Kyprianou.ProofPreparation.nnreal_coe_tendsto_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:03.413016+00:00
-- url     : https://prove2.me/theorems/e8465320-dd19-40f0-bf83-7d2215aabe1d
-- title:
--   Kyprianou.ProofPreparation.nnreal_coe_tendsto_left
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.nnreal_coe_tendsto_left from oversized parent candidate 90e7910cafc628d87d9555fc15dcd1e42ff7827cd4f9408e83e0aa8a6c952cc2.
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
theorem nnreal_coe_tendsto_left (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by sorry
end Kyprianou.ProofPreparation
