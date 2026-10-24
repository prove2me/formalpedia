-- Prove2me | Theorems.Thm_OAI_PiExponent_eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
-- name    : OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:36:34.106379+00:00
-- url     : https://prove2.me/theorems/5bfe6eea-fb13-481b-a8d3-b6a0930c42aa
-- title:
--   Bound the number of centers by weighted jet dimension
-- statement:
--   At each sufficiently large admissible cutoff, surjectivity onto all transverse jet coefficients bounds the target coefficient count by the source monomial count. Weighted simplex lattice-count asymptotics, with the strict target cutoff and non-strict source cutoff having the same leading volume, imply the spatial volume bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
open scoped BigOperators

theorem OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
    (m K : Nat) (alpha : Rat) (w : Fin m → Nat)
    (hm : 0 < m) (hK : 0 < K) (halpha : 0 < alpha)
    (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (htrans : OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c) :
    (K : Rat) * alpha ^ m ≤ 1 := by sorry
