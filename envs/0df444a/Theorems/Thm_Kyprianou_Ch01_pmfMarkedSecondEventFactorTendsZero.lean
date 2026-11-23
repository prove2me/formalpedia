-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfMarkedSecondEventFactorTendsZero
-- name    : Kyprianou.Ch01.pmfMarkedSecondEventFactorTendsZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:13:45.790295+00:00
-- url     : https://prove2.me/theorems/df4bcef6-32a5-4547-86cf-08dd1b93b8db
-- title:
--   PMF-averaged second-arrival exponential chance vanishes without offspring moment bounds
-- statement:
--   For any offspring PMF and fixed initial y, the expected chance 1-exp(-rate*(y+k)*t) of a second jump vanishes as t decreases to zero. This follows from the Proved weighted Tannery theorem 2afce52b-c7f8-406d-8ac0-5857c9ca3d75. No finite offspring mean is assumed.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfMarkedSecondEventFactorTendsZero
    (p : PMF ℕ) (rate : ℝ≥0) (y : ℕ) :
    Tendsto
      (fun t : ℝ => ∑' k : ℕ, (p k).toReal *
        (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  sorry
