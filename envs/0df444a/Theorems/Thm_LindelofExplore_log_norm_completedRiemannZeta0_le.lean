-- Prove2me | Theorems.Thm_LindelofExplore_log_norm_completedRiemannZeta0_le
-- name    : LindelofExplore.log_norm_completedRiemannZeta0_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T16:38:33.095547+00:00
-- url     : https://prove2.me/theorems/d41d01cf-8356-4332-876a-49c3c1ea2ea9
-- title:
--   Log-norm bound for the completed zeta function on Re s ≥ 2
-- statement:
--   For every complex number $s$ with real part at least $2$, the logarithm of the norm of the completed Riemann zeta function $\Lambda_0(s)$ (Mathlib's `completedRiemannZeta₀`, the completed zeta function with its poles removed) is at most $3 + \mathrm{Re}(s)\log \mathrm{Re}(s)$.

import Mathlib
open Complex MeasureTheory Set Filter Real
open scoped Topology

namespace LindelofExplore
theorem log_norm_completedRiemannZeta0_le {s : ℂ} (hs : 2 ≤ s.re) : Real.log ‖completedRiemannZeta₀ s‖ ≤ 3 + s.re * Real.log s.re := by sorry
end LindelofExplore
