-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_theorem_1_convex
-- name    : LinearPriceRule.Concave.theorem_1_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:05.232895+00:00
-- url     : https://prove2.me/theorems/f554625b-d80c-46f1-860e-3ed18857d74c
-- title:
--   Theorem 1 (convex case, interior optimum), p. 9 — if P_A is convex then an interior optimal price P** is at most P* = (P_m + c)/2
-- statement:
--   Consider a market with maximum price $P_m$, marginal cost $0 \le c < P_m$, saturation quantity $Q_{\max} > 0$ and inverse demand $P_A$ with $P_A(0) = P_m$, non-increasing and continuous on $[0, Q_{\max}]$. If $P_A$ is convex on $[0, Q_{\max}]$, then for every quantity $Q^{**}$ maximizing the profit $(P_A(Q) - c)\,Q$ over $[0, Q_{\max}]$ with $Q^{**} < Q_{\max}$,
--   $$
--   P^{**} = P_A(Q^{**}) \;\le\; P^* = \frac{P_m + c}{2}.
--   $$
--
--   With a convex inverse demand, the linear pricing rule over-prices.
--
--   **Formalization Note** The hypothesis $Q^{**} < Q_{\max}$ (an interior optimum) is added: the paper's proof equates marginal revenue with marginal cost. It is necessary: for $P_A(Q) = 5 - Q/10$ on $[0, 1]$ and $c = 1$, the optimum is the corner $Q^{**} = 1$ with $P^{**} = 4.9 > P^* = 3$.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 9, Theorem 1 (convex case; proof p. 23)

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem theorem_1_convex (M : Market) (hM : M.Standing)
    (hconv : ConvexOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q)
    (hint : Q < M.Qmax) :
    M.PA Q ≤ linPrice M := by sorry
end LinearPriceRule.Concave
