-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_proposition_1
-- name    : InnovAlloc.Optimal.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:26.169384+00:00
-- url     : https://prove2.me/theorems/3ca86927-cea3-4415-8bda-bb08c6e5fb12
-- title:
--   Proposition 1, pp. 11, 37–38 — endpoint domination at fixed investment
-- statement:
--   Fix $\alpha\in[0,1]$, $\gamma\in(0,1)$, a positive total investment $B$, and a split $(B-b_2,b_2)$ with $0\le b_2\le B/2$. For every effort equilibrium at that split, at least one of the two endpoint allocations $(B,0)$ and $(B/2,B/2)$ has an equilibrium yielding the principal at least as much profit:
--
--   $$\Pi(B-b_2,b_2)\le\max\{\Pi(B,0),\Pi(B/2,B/2)\}.$$
--
--   This reduces the search over all asymmetric allocations at a fixed total to the two strategies compared in Theorem 1.
--
--   **Formalization Note** The paper's literal wording that every optimum “must” be an endpoint fails when all allocations earn zero. Its proof establishes this endpoint-domination content; the Lean statement quantifies over the relevant equilibria explicitly.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 11, Proposition 1; pp. 37–38, proof

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Proposition 1, pp. 11 and 37–38, read as domination by an endpoint at fixed total
    investment; its literal necessity claim has zero-profit exceptions. -/
theorem proposition_1 (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B)
    (b2 : ℝ) (hb2 : 0 ≤ b2) (hb2B : b2 ≤ B / 2)
    (x1 x2 : ℝ) (heq : IsEquilibrium α γ (B - b2) b2 x1 x2) :
    (∃ z1 z2, IsEquilibrium α γ B 0 z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ B 0 z1 z2) ∨
    (∃ z1 z2, IsEquilibrium α γ (B / 2) (B / 2) z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ (B / 2) (B / 2) z1 z2) := by sorry

end InnovAlloc.Optimal
