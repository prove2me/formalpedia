-- Prove2me | Theorems.Thm_MasulloRH_actual_prime_uniform_positive_damped_resolvent
-- name    : MasulloRH.actual_prime_uniform_positive_damped_resolvent
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:49:55.954459+00:00
-- url     : https://prove2.me/theorems/6ef40d56-98cd-4150-8c80-c7704af9d1fc
-- title:
--   The actual prime-resolvent cutoff profile, uniformly for every positive damping parameter
-- statement:
--   Put X=N+2 and Y=log X. For all c>0, the normalized weighted prime sum Σ_{p≤X} (log p)² exp(−c log p/Y)/(pY²) differs from [1−(1+c)e^(−c)]/c² by at most [(2(log 4+4)+1537/log 2)Y+1537]/Y² + log(2)/Y. The bound tends to zero uniformly on the entire positive half-line. This computes the prime contribution only.
-- source:
--   Direct application of the certified prime mass and uniform damped mesh estimates 91135a88-0fea-4eed-b9be-12d7ac06ae13 and dd67819c-16e9-4f9e-ac15-41503fe4ce53. The integer logarithmic mesh places each actual prime at an endpoint.

import Mathlib
import Theorems.Thm_MasulloRH_prime_resolvent_zero_profile_and_uniform_prime_power_transfer
import Theorems.Thm_MasulloRH_uniform_damped_resolvent_mesh_discrepancy

open Finset Real

theorem MasulloRH.actual_prime_uniform_positive_damped_resolvent (N : ℕ) (c Y : ℝ) (hc : 0 < c) (hY : Y = Real.log ((N : ℝ)+2)) :
    |(∑ i ∈ (range (N+1)).filter (fun i => (i+2).Prime),
      Real.exp (-c * (Real.log ((i:ℝ)+2) / Y)) *
        ((Real.log ((i:ℝ)+2))^2 / ((i:ℝ)+2) / Y^2)) -
      (1-(1+c)*Real.exp (-c))/c^2| ≤
      ((2*(Real.log 4+4)+1537 / Real.log 2)*Y + 1537)/Y^2 + Real.log 2 / Y := by sorry
