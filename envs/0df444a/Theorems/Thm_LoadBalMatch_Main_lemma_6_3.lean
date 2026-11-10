-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_6_3
-- name    : LoadBalMatch.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:56.882402+00:00
-- url     : https://prove2.me/theorems/6db59650-685f-4274-8473-fb5c51504f25
-- title:
--   Lemma 6.3 — a balanced fractional matching is a convex combination of maximum matchings
-- statement:
--   Let $H$ be a graph on the finite set $V$ and let $x$ be a balanced fractional matching on $H$, i.e. $x\in P(H)$ minimises $\eta(x)=\sum_v(1-x_v)^2$ over the matching polytope $P(H)$ (with odd-set constraints). Then $x$ is a convex combination of incidence vectors of **maximum** matchings of $H$: there are maximum matchings $M_1,\dots,M_k$ of $H$ and weights $w_1,\dots,w_k\ge 0$ with $\sum_i w_i=1$ such that
--   $$x_e=\sum_{i=1}^k w_i\,\mathbf 1[e\in M_i]\qquad\text{for every pair } e.$$
--
--   The lemma is the bridge from the convex objective $\eta$ to the combinatorics of maximum matchings; Lemmas 6.8, 6.9 and 7.11 rest on it.
--
--   Differences from the source:
--   - encoding: x is a convex combination of maximum matchings → a finite family M : Fin k → Finset (Sym2 V) of maximum matchings of H with weights w ≥ 0 summing to 1 and x e = Σ_i w_i·1[e ∈ M_i] for every pair e; reason: definition of a convex combination of incidence vectors
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 27, Lemma 6.3

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching

namespace LoadBalMatch.Main

theorem lemma_6_3 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : Sym2 V → ℝ) (hx : IsBalanced H x) :
    ∃ (k : ℕ) (M : Fin k → Finset (Sym2 V)) (w : Fin k → ℝ),
      (∀ i, IsMaximumMatching H (M i)) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ e, x e = ∑ i, w i * (if e ∈ M i then 1 else 0) := by sorry

end LoadBalMatch.Main
