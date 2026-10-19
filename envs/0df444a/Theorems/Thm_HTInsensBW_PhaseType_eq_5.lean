-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_eq_5
-- name    : HTInsensBW.PhaseType.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:30.939242+00:00
-- url     : https://prove2.me/theorems/a01fb3bd-8b44-400b-b2e4-dda07e8ab03e
-- title:
--   (5), p. 6 — the weighted proportionally fair allocation exists, is unique and has Lagrange multipliers
-- statement:
--   Let $H$ be a $0/1$ routing matrix in which every route uses at least one link, let the capacities $C_\ell$ and the weights $\kappa_r$ be positive, and let $\mathbf m=(m_r)$ be any vector of route counts. Then the weighted proportionally fair allocation problem
--   $$\max_x\ \sum_r\kappa_rm_r\log x_r\quad\text{s.t.}\quad\sum_{r:\ell\in r}m_rx_r\le C_\ell\ \forall\ell,\quad x\ge0,\quad x_r=0\text{ when }m_r=0$$
--   has exactly one optimal solution, and every optimal solution has Lagrange multipliers $p_\ell\ge0$ for the capacity constraints, with complementary slackness, such that
--   $$x_r=\begin{cases}\dfrac{\kappa_r}{\sum_{\ell:\ell\in r}p_\ell}&m_r>0,\\[4pt] 0&\text{otherwise.}\end{cases}$$
--
--   This makes the policy well defined: every other statement of the mission takes an allocation function satisfying the optimality conditions, and this theorem shows that such a function exists and is unique.
--
--   **Formalization Note** Uniqueness is not printed, but "the optimal solution" (p. 5) presupposes it. The multipliers need not be unique, so existence is asserted. "Every route uses a link" and "$C_\ell>0$" are implicit in the paper's model (a route is "a set of consecutive links"; $C_{\min}$ divides in (31)) and are stated explicitly.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 6, (5); problem (2)–(4), pp. 5–6

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBW.PhaseType

/-- **(5), p. 6 — the weighted proportionally fair allocation exists, is unique, and has
Lagrange multipliers.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 6, (5); problem (2)–(4), pp. 5–6.)
For every vector of route counts `m`, the problem (2)–(4) has exactly one optimal solution `x`, and
for every optimal `x` there are multipliers `p_ℓ ≥ 0` (complementary slackness) with
`x_r = κ_r / Σ_{ℓ : ℓ ∈ r} p_ℓ` when `m_r > 0` (and `x_r = 0` otherwise, part of the problem).

**Formalization Note** Uniqueness is not printed but is presupposed by "the optimal solution"
(p. 5). The multipliers need not be unique; existence is asserted. Hypotheses: 0/1 routing matrix,
every route uses a link, positive capacities and weights (the standing assumptions of §2, the
last two implicit on the page). -/
theorem eq_5 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1)
    (hC : ∀ ℓ, 0 < N.C ℓ) (hκ : ∀ r, 0 < N.κ r) :
    ∀ m : Fin R → ℕ, (∃! x, IsWPFAllocation N m x) ∧
      ∀ x, IsWPFAllocation N m x → ∃ p, IsKKTMultiplier N m x p := by sorry

end HTInsensBW.PhaseType
