-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_lemma_3
-- name    : HochbaumShmoys.Uniform.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:54.624787+00:00
-- url     : https://prove2.me/theorems/25361713-7d69-4004-a736-dc0ad1b3f22c
-- title:
--   Lemma 3 — a truly feasible packing gives a path from initial to success (p. 547)
-- statement:
--   Let $N\ge2$, $\delta=1/N$, $m\ge1$, and consider a normalized instance: bins $\beta_1\ge\beta_2\ge\dots\ge\beta_m>0$ with $\beta_1=1$, and pieces $\pi_1,\dots,\pi_n$ with $0<\pi_j\le1$. If there is a truly feasible packing, i.e. a map $\sigma$ with
--   $$\sum_{j:\ \sigma(j)=t}\pi_j\le\beta_t\quad\text{for every bin } t,$$
--   then the layered graph of all-pack for this instance contains a directed path from the initial node to the node success.
--
--   This is the half of the correctness of all-pack that justifies its negative answer: if no path exists, no truly feasible packing exists.
--
--   **Formalization Note** The standing assumptions of §3 are hypotheses: bins sorted by non-increasing size and normalized so the largest is $1$, $1/\delta$ a positive integer, $\delta\le1/2$. The path is a chain of arcs of the graph (reflexive–transitive closure of the arc relation). The graph uses $w+1$ classes and capped slack counters (see the definitions).
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 547, Lemma 3

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

theorem lemma_3 (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ) (π : Fin n → ℝ)
    (hβ : Antitone β) (hβ0 : β ⟨0, hm⟩ = 1) (hβpos : ∀ t, 0 < β t)
    (hπ : ∀ j, 0 < π j ∧ π j ≤ 1)
    (hfeas : ∃ σ : Fin n → Fin m, IsTrulyFeasible π β σ) :
    Relation.ReflTransGen (Arc N β π) (initialNode N π hm) Node.success := by sorry

end HochbaumShmoys.Uniform
