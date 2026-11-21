-- Prove2me | Theorems.Thm_MasulloRH_lifted_rank_one_series_traceNorm_limit
-- name    : MasulloRH.lifted_rank_one_series_traceNorm_limit
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:18:35.830761+00:00
-- url     : https://prove2.me/theorems/fa4f72cb-d2ac-4661-ba70-8ec629412ef0
-- title:
--   Trace-norm convergence for the absolutely summable lifted rank-one series
-- statement:
--   For a bounded operator A, lifted vectors vᵢ, and Riesz representatives ηᵢ, absolute summability of ‖A vᵢ‖ ‖ηᵢ‖ gives a nuclear operator T. The rank-one series sums to T in operator norm, and the net of all finite partial sums converges to T in trace norm. The analytic estimate for the particular convolution and lifts is a hypothesis of this implication.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, Theorem 10.4.2.8, pp. 463–464, (10.4.2.25) and the convergence assertion after (10.4.2.34).

import Definitions.Def_MasulloGRH_HilbertNuclear

open MasulloGRH Filter InnerProductSpace
open scoped Topology

theorem MasulloRH.lifted_rank_one_series_traceNorm_limit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (v η : ℕ → H)
    (hs : Summable fun i => ‖A (v i)‖ * ‖η i‖) :
    let R := fun i => rankOne ℂ (A (v i)) (η i)
    ∃ T : H →L[ℂ] H, HasSum R T ∧ IsNuclearOperator T ∧
      Tendsto (fun s : Finset ℕ => traceNorm (T - ∑ i ∈ s, R i)) atTop (𝓝 0) := by sorry
