-- Prove2me | Theorems.Thm_GRH_coprime_moebius_reciprocal_sums_decay_logarithmically
-- name    : GRH.coprime_moebius_reciprocal_sums_decay_logarithmically
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:47:33.480205+00:00
-- url     : https://prove2.me/theorems/f598175e-cbb7-442e-9510-2ed3a33ea277
-- title:
--   Logarithmic decay of the coprime Möbius reciprocal sum
-- statement:
--   For each fixed positive q, the absolute value of the sum of μ(n)/n over 1 ≤ n ≤ U with gcd(n,q)=1 is at most K(q)/(1+log(U+1)), for every cutoff U.
-- source:
--   Unconditional fixed-modulus estimates for the centered Möbius progression sum in https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . El Marraki inequality https://prove2.me/submissions/4c341bba-f2d7-47f2-ab1b-55d9305b6115 and prime-square reindexing https://prove2.me/submissions/ee3f3cdf-1dd7-484d-9427-d6451ad0a244 .

import Definitions.Def_GRH_LogarithmicMoebius

open Finset Filter Topology GRH.LogarithmicMoebius

theorem GRH.coprime_moebius_reciprocal_sums_decay_logarithmically (q : ℕ) [NeZero q] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ, |GRH.reducedMoebiusHarmonic q U| * scale U ≤ K := by sorry
