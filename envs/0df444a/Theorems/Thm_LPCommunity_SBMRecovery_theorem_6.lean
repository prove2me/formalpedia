-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_theorem_6
-- name    : LPCommunity.SBMRecovery.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:56.994587+00:00
-- url     : https://prove2.me/theorems/7c599f77-2ac1-487b-8628-c9267e857c35
-- title:
--   Theorem 6, p. 15 — the metric LP relaxation recovers the planted bisection of G_{n,p,q} w.h.p. when p − q > 1/2
-- statement:
--   Let $p,q$ be constants with $0<q<p<1$ and
--   $$
--   p-q>\tfrac12 .
--   $$
--   Let $G\sim\mathcal G_{n,p,q}$ be the stochastic block model on $n$ (even) nodes with a uniformly random planted bisection $V_1,V_2$. Then, with probability tending to $1$ as $n\to\infty$, the LP relaxation (LP-P) recovers the planted bisection: the cut vector of $V_1,V_2$ is the unique optimal solution of (LP-P).
--
--   This is the paper's recovery guarantee for the very dense regime. It shows that the metric LP succeeds in a nontrivial region of the parameters, in contrast to the failure results of Theorems 7 and 8.
--
--   **Formalization Note** "With high probability" is the limit along even $n=2m$, $m\to\infty$. The recovery event is evaluated at the bisection drawn by the model. (LP-P) is over symmetric zero-diagonal arrays, with no box constraints.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 15, Theorem 6

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Theorem 6 (p. 15): for constants `0 < q < p < 1` with `p − q > 1/2`, the LP relaxation (LP-P)
recovers the planted bisection of `G ∼ G_{n,p,q}` with high probability (`n = 2m → ∞`). -/
theorem theorem_6 (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1) (h : p - q > 1 / 2) :
    Tendsto (fun m : ℕ => sbmProb (2 * m) p q (fun V1 G => LPCommunity.LPRecovery.LPRecovers G V1))
      atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
