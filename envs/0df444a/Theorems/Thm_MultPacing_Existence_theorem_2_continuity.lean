-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_2_continuity
-- name    : MultPacing.Existence.theorem_2_continuity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:36.246983+00:00
-- url     : https://prove2.me/theorems/476de9bb-4896-4fb2-a910-ed77c37ef0ac
-- title:
--   Proof of Theorem 2, "Continuity of utility in all strategies", p. 12 — x_ij, s_ij and u_i are continuous in α
-- statement:
--   Fix a pacing game, $\epsilon>0$ and any $H$, and consider the $(\epsilon,H)$-smoothed pacing game. For every buyer $i$ and good $j$, the allocation $x_{ij}(\alpha)$, the payment $s_{ij}(\alpha)=x_{ij}(\alpha)p_{ij}(\alpha)$ and the utility $u_i(\alpha)$ are continuous functions of the whole profile of pacing multipliers on the strategy space:
--   $$
--   \alpha\mapsto x_{ij}(\alpha),\quad \alpha\mapsto s_{ij}(\alpha),\quad \alpha\mapsto u_i(\alpha)\qquad\text{are continuous on }[0,1]^N .
--   $$
--
--   This is one of the hypotheses of the pure Nash equilibrium existence theorem (Debreu, Glicksberg, Fan) that proves Theorem 2.
--
--   **Formalization Note** Continuity is `ContinuousOn` on the cube `Set.univ.pi (fun _ => Set.Icc 0 1)` in $\mathbb R^N$ with the product topology.
--
--   Differences from the source:
--   - generalization: the bullet is argued under Theorem 2's hypotheses ($H>M/\epsilon$, and Definition 3's $H>0$) → every real $H$; reason: the two budget branches of the utility agree at $0$ for every $H$, so continuity never uses a bound on $H$, and the statement specializes to the source's case.
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 2, bullet "Continuity of utility in all strategies"

import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2_continuity {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℝ) (hε : 0 < ε) :
    (∀ i j, ContinuousOn (fun α => smAlloc P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i j, ContinuousOn (fun α => smPay P ε α i j) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i, ContinuousOn (fun α => smUtility P ε H α i) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) := by sorry

end MultPacing.Existence
