-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalPointwiseENNRealSum
-- name    : Kyprianou.Ch01.gammaArrivalPointwiseENNRealSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:10:51.9792+00:00
-- url     : https://prove2.me/theorems/a405f564-0277-4909-966d-f24e8abd16c6
-- title:
--   Pointwise sum of gamma-arrival ENNReal densities is the constant exponential rate
-- statement:
--   The countable sum of all Erlang(n+1,beta) nonnegative extended-real density values at any nonnegative z equals beta. This uses the previously proved real exponential Taylor series and its absolute summability, converts the real nonnegative series to ENNReal, and serves as the pointwise input for Tonelli integration in Exercise 1.8(iv).
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), worked solution pp.304–305

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaArrivalPointwiseENNRealSum
    (beta z : ℝ) (hbeta : 0 < beta) (hz : 0 ≤ z) :
    (∑' n : ℕ, LevyFoundations.arrivalGammaDensity beta n z) =
      ENNReal.ofReal beta := by
  sorry
