-- Prove2me | Theorems.Thm_GenEllipPot_Potential_scalar_log_bound
-- name    : GenEllipPot.Potential.scalar_log_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:13.760859+00:00
-- url     : https://prove2.me/theorems/11367ffb-a003-4066-aada-706c5302586d
-- title:
--   Proof of Theorem 2.1, p. 10: x ≤ 2 log(1+x) for 0 ≤ x ≤ 1
-- statement:
--   For every real $x\in[0,1]$,
--
--   $$x\le 2\log(1+x).$$
--
--   This scalar comparison converts a bounded posterior quadratic form into a logarithmic increment in the proof of the elliptical potential bound.
-- source:
--   Hamidi & Bayati, The Elliptical Potential Lemma for General Distributions with an Application to Linear Thompson Sampling, arXiv:2102.07987v3, p. 10, proof of Theorem 2.1, before (A.2)

import Mathlib

namespace GenEllipPot.Potential

/-- Scalar inequality used in the proof of Theorem 2.1, p. 10. -/
theorem scalar_log_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ 2 * Real.log (1 + x) := by sorry

end GenEllipPot.Potential
