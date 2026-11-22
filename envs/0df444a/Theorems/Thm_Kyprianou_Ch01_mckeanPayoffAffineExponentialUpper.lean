-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanPayoffAffineExponentialUpper
-- name    : Kyprianou.Ch01.mckeanPayoffAffineExponentialUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:46:21.588557+00:00
-- url     : https://prove2.me/theorems/9f74d11d-b7f4-48ac-b8ac-6e4f2bf1ab31
-- title:
--   Every exercise payoff is below its global affine-exponential tangent at any supporting state
-- statement:
--   Apply the newly proved weighted tangent inequality phi exp(z−u)+exp(−phi(z−u))≥1+phi. Multiply by positive exp(u)/phi and rewrite exp(u)*exp(z−u)=exp(z) to obtain the globally valid upper bound on K−exp(z) by its affine-exponential tangent at u. This source-faithful analytic lemma is the payoff/exercise-side component of the original McKean affine supporting majorant; no probabilistic assumptions are needed. The theorem explicitly imports its now-Proved weighted exponential tangent child.
-- source:
--   Kyprianou (2006) Ch1 McKean perpetual put, affine upper tangent inequality.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_mckeanWeightedExponentialTangent
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanPayoffAffineExponentialUpper
    (K phi u z : ℝ) (hphi : 0 < phi) :
    K - Real.exp z ≤
      (K - (1 + 1 / phi) * Real.exp u) +
        (Real.exp u / phi) * Real.exp (-phi * (z - u)) := by sorry
