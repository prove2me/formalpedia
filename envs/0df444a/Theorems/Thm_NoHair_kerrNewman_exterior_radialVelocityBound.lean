-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_radialVelocityBound
-- name    : NoHair.kerrNewman_exterior_radialVelocityBound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:44:24.954798+00:00
-- url     : https://prove2.me/theorems/744f6859-6d54-4439-a20b-6e34fb1538d7
-- title:
--   An optical upper bound on the outward radial speed of exterior causal vectors
-- statement:
--   At every point outside the outer horizon, a causal tangent vector with nonnegative Cartesian time component satisfies $m\,dr(v)\leq(r-r_+)\,dt(v)$. Thus an increasing-time causal signal near the horizon has outward radial speed at most $(r-r_+)/m$. This estimate is uniform in angle and includes extremality.
-- source:
--   B. Carter, Global structure of the Kerr family of gravitational fields, https://doi.org/10.1103/PhysRev.174.1559. The displayed bound is obtained directly from the null Kerr–Schild form and the factorization of the horizon polynomial.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_exterior_radialVelocityBound (m a e : ℝ)
    (hp : IsKerrNewmanBlackHoleParams m a e) (x : kerrNewmanSpacetime a)
    (hx : kerrNewmanOuterRadius m a e < ksRadius a x.val) (v : E4)
    (ht : 0 ≤ v 0) (hv : kerrNewmanMetricField m a e x v v ≤ 0) :
    m * fderiv ℝ (ksRadius a) x.val v ≤ (ksRadius a x.val - kerrNewmanOuterRadius m a e) * v 0 := by sorry
