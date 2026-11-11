-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_edge_covariance
-- name    : MatchingNearLinear.Glauber.edge_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:57:31.068284+00:00
-- url     : https://prove2.me/theorems/e9247ea3-ba65-4a25-91ab-61aaebb4b0ec
-- title:
--   Proposition 4.1 — Edge covariance
-- statement:
--   For every finite simple graph, every $s>0$, and every choice of edge activities $0<\lambda_e\le s$, the edge occupation vector $X$ satisfies, after every feasible present/absent edge pin,
--
--   $$\operatorname{Cov}(X)\preceq\widehat C(s)\operatorname{Diag}(EX),\quad \widehat C(s)=\begin{cases}\min\{7+48s,(1-s)^{-1}\},&0<s<1,\\7+48s,&s\ge1.\end{cases}$$
--
--   Moreover $\widehat C(0)=1$, the function is nondecreasing on $[0,\infty)$, and $|\widehat C(s)-1|\le As$ for all sufficiently small positive $s$, with absolute $A>0$. Covariance is mean-normalized, not variance-normalized. These bounds verify the spectral-stability hypothesis for matching laws.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labeled edge lists → vertices Fin n and edges Fin m with distinct endpoints and injective unordered endpoint map; reason: every finite source graph admits this encoding, including isolated vertices and disconnected graphs
--   - encoding: deterministic coordinates are omitted → the covariance quadratic form is stated on all coordinates; reason: zero covariance rows impose no additional restrictions, and testing vectors supported on random coordinates recovers exactly the omitted-coordinate inequality
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Proposition 4.1, printed p. 19 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_CovarianceRate

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem edge_covariance :
    (∀ (n m : ℕ) (G : Input n m) (s : ℝ), 0 < s → ∀ lam : Fin m → ℝ,
      ActivityBound lam s → ∀ τ : Fin m → Option Bool,
      0 < eventMass (matchingLaw G lam) indicator τ →
      CovarianceBound (edgeConditional G lam τ) (matchingRate s)) ∧
    matchingRate 0 = 1 ∧ MonotoneOn matchingRate (Set.Ici (0:ℝ)) ∧
    (∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ s : ℝ, 0 < s → s < d →
      |matchingRate s - 1| ≤ A*s) := by sorry

end MatchingNearLinear.Glauber
