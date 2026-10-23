-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_theorem_1_concave
-- name    : LinearPriceRule.Concave.theorem_1_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:00.166209+00:00
-- url     : https://prove2.me/theorems/9c8f5ffa-d392-49cb-8a3f-02427569f0da
-- title:
--   Theorem 1 (concave case), p. 9 — if P_A is concave then every optimal price P** is at least the linear price P* = (P_m + c)/2
-- statement:
--   Consider a market with maximum price $P_m$, marginal cost $0 \le c < P_m$, saturation quantity $Q_{\max} > 0$ and inverse demand $P_A$ with $P_A(0) = P_m$, non-increasing and continuous on $[0, Q_{\max}]$. If $P_A$ is concave on $[0, Q_{\max}]$, then for every quantity $Q^{**}$ maximizing the profit $(P_A(Q) - c)\,Q$ over $[0, Q_{\max}]$,
--   $$
--   P^{**} = P_A(Q^{**}) \;\ge\; P^* = \frac{P_m + c}{2}.
--   $$
--
--   The linear pricing rule therefore under-prices whenever the true inverse demand is concave. This is the first step of the proof of Proposition 5.
--
--   **Formalization Note** Concavity is of the inverse demand $P_A$ in $Q$, on $[0, Q_{\max}]$. No differentiability is assumed (the paper's proof uses a Taylor expansion; the statement does not need it). The conclusion holds for every maximizer, not a chosen one.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 9, Theorem 1 (concave case; proof p. 23)

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem theorem_1_concave (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q) :
    linPrice M ≤ M.PA Q := by sorry
end LinearPriceRule.Concave
