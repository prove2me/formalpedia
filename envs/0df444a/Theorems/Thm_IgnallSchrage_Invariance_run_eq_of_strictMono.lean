-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_run_eq_of_strictMono
-- name    : IgnallSchrage.Invariance.run_eq_of_strictMono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:05.183343+00:00
-- url     : https://prove2.me/theorems/572701fc-32e9-4568-8158-0b7fa8676bac
-- title:
--   p. 411 — bounds with the same ranking make the branch-and-bound procedure follow the same path
-- statement:
--   Let $LB$ and $LB'$ be two bound functions on nodes, and let $\varphi:\mathbb R\to\mathbb R$ be strictly increasing. Suppose that
--   $$
--   LB'(J_r)=\varphi\big(LB(J_r)\big)
--   $$
--   for every node $J_r$ ($r$ distinct jobs) with $1\le r\le n-1$. Then the branch-and-bound procedure of p. 402 follows the same path with $LB'$ as with $LB$: for every $k$, the list of nodes after $k$ steps is the same,
--   $$
--   \mathrm{run}_{LB'}(k)=\mathrm{run}_{LB}(k).
--   $$
--
--   This is the paper's "the ranking of the lower bounds is unaffected …, implying that the path taken by the branch-and-bound procedure is also unaffected", stated for any order-preserving change of the bounds. The shift ($\varphi(x)=x+\text{const}$) and the scale ($\varphi(x)=Hx$) are special cases.
--
--   **Formalization Note** The procedure is the deterministic one of the definition `Procedure`, ties included. Since $\varphi$ is strictly increasing, $LB'(x)\le LB'(y)$ exactly when $LB(x)\le LB(y)$, so every comparison, ties included, comes out the same. The hypothesis concerns only nodes with $1\le r\le n-1$, the only nodes the procedure compares: the root is alone on the initial list.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (the ranking of the lower bounds is unaffected … the path taken by the branch-and-bound procedure is also unaffected)

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Invariance

/-- p. 411: if two bound functions rank the nodes the procedure compares in the same way —
`LB' J = φ (LB J)` for a strictly increasing `φ` at every node `J_r` with `1 ≤ r ≤ n - 1` —
then the branch-and-bound procedure follows the same path with both: the lists agree after
every number of steps. -/
theorem run_eq_of_strictMono {n : ℕ} (LB LB' : List (Fin n) → ℝ) (φ : ℝ → ℝ)
    (hφ : StrictMono φ)
    (h : ∀ J : List (Fin n), J.Nodup → 1 ≤ J.length → J.length + 1 ≤ n → LB' J = φ (LB J)) :
    ∀ k : ℕ, IgnallSchrage.Makespan.run LB' k = IgnallSchrage.Makespan.run LB k := by sorry

end IgnallSchrage.Invariance
