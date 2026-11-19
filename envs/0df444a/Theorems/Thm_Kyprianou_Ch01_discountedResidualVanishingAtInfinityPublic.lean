-- Prove2me | Theorems.Thm_Kyprianou_Ch01_discountedResidualVanishingAtInfinityPublic
-- name    : Kyprianou.Ch01.discountedResidualVanishingAtInfinityPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:18:40.641021+00:00
-- url     : https://prove2.me/theorems/7a097040-4a7e-4720-a636-bc8eb2e0abff
-- title:
--   Discounted exponential residual vanishes on never-crossing bounded paths
-- statement:
--   If a real path at integer times never exceeds an upper barrier x, the positive-discounted exponential exp(theta*f(n)-q*n) tends to zero when theta is nonnegative and q is strictly positive. This is a direct deterministic geometric domination, needed in the infinite-horizon limit of the Brownian first passage stopped exponential.
-- source:
--   Kyprianou (2006) Exercise 1.10(ii), worked solution printed page 306, limit on never-crossing sample paths.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
open Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.discountedResidualVanishingAtInfinityPublic
    (f : ℕ → ℝ) (x theta q : ℝ)
    (hbounded : ∀ n, f n ≤ x)
    (htheta : 0 ≤ theta) (hq : 0 < q) :
    Tendsto (fun n : ℕ => Real.exp (theta * f n - q * (n : ℝ)))
      atTop (nhds 0) := by sorry
