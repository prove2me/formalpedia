-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_14
-- name    : NAMatchEst.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:46:39.650988+00:00
-- url     : https://prove2.me/theorems/9e7773ca-1b5c-47af-bd48-dfc77328bc15
-- title:
--   Theorem 14 — extended lower bound $\Omega(Q)$ when $Q^2\alpha^3\log^3 N=o(N^3)$
-- statement:
--   Here $\mu(G)$ is the maximum matching size; logarithms are to base 2. Let $\alpha,Q:\mathbb N\to\mathbb R$ with $\alpha(N)\ge1$ and $Q(N)\ge1$ for all $N$, and suppose
--
--   $$
--   \frac{\alpha(N)}{N^{1/2}}\to0\qquad\text{and}\qquad\frac{Q(N)^2\,\alpha(N)^3\log^3 N}{N^3}\to0\qquad(N\to\infty).
--   $$
--
--   1. There are $c>0$ and $N_0$ such that for every $N\ge N_0$, every randomized non-adaptive adjacency-list algorithm that returns an $\alpha(N)$-approximation of $\mu(G)$ (that is, $\mu(G)/\alpha(N)\le\widehat\mu\le\mu(G)$) with probability at least $2/3$ on every simple $N$-vertex graph makes at least $c\,Q(N)$ distinct queries in the worst case.
--   2. In particular, for every fixed $0<\delta<1/2$ there are $c>0$ and $N_0$ such that for $N\ge N_0$ every such algorithm for $\alpha=N^\delta$ makes at least
--   $$
--   c\cdot\frac{N^{1.5-1.5\delta}}{\log^2 N}
--   $$
--   queries, which is $\tilde\Omega(N^{1.5-1.5\delta})$.
--
--   This is the simple-graph extension of the earlier lower bound, used for Theorem 9(i).
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - encoding: any randomized non-adaptive algorithm → every RandAlg (finite seed space); reason: at a fixed n the success probabilities on the finitely many inputs of any algorithm with a given worst-case query bound are a convex combination of those of deterministic algorithms, realized by a finite mixture with the same bound (Carathéodory); same theorem
--   - encoding: worst-case number of queries, identical queries answered once (p.20) → DistinctCostLE: distinct queries on every seed of positive probability, for every bound q; reason: the paper's cost measure
--   - encoding: α = o(N^{1/2}) and Q² α³ log³ N = o(N³) → Tendsto (α N / N^{1/2}) atTop (𝓝 0) and Tendsto (Q N² α N³ (log₂ N)³ / N³) atTop (𝓝 0); reason: the definition of little-o
--   - reading: Ω(Q) → c · Q N with c > 0 and N₀ chosen after α and Q; reason: asymptotic notation
--   - reading: this implies the lower bound Ω̃(N^{1.5−1.5δ}) by taking Q = N^{1.5−1.5δ}/log² N → a second conjunct: ∀ δ ∈ (0, 1/2), ∃ c > 0, N₀ with c · N^{1.5−1.5δ}/(log₂ N)² ≤ q for α = N^δ; reason: the Ω(Q) bound for the stated Q, which is the Ω̃ bound the sentence derives
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 14, p.198 (PDF 202)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_Supplement_DistinctCostLE

namespace NAMatchEst.Supplement

open Filter Topology

/-- **Theorem 14.** Let `α = α(N) ⩾ 1` satisfy `α = o(N^{1/2})`, and let `Q = Q(N) ⩾ 1` satisfy
`Q² α³ log³ N = o(N³)`. Any randomized algorithm that, on every `N`-vertex simple graph, returns an
`α` approximation to the maximum matching size with probability at least `2/3` requires `Ω(Q)`
non-adaptive adjacency list queries in the worst case. In particular, … For each fixed
`0 < δ < 1/2`, this implies the lower bound `Ω̃(N^{1.5−1.5δ})` by taking
`Q = N^{1.5−1.5δ}/log² N`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 14, p.198 (PDF 202).

**Formalization Note**
1. `α` and `Q` are real functions of `N`, at least one everywhere; the little-o hypotheses are
   limits along `N → ∞`. `Ω(Q)`: a constant `c > 0` and a threshold `N₀`, chosen after `α`, `Q`.
2. The second conjunct is the "in particular" sentence for `α = N^δ`: the bound
   `c · N^{1.5−1.5δ}/log² N`, i.e. `Ω(Q)` for the stated `Q`.
3. Success with probability `⩾ 2/3` on every simple graph on `Fin N` under every list ordering;
   distinct queries on seeds of positive probability (`DistinctCostLE`); `log` base 2. -/
theorem theorem_14 (α Q : ℕ → ℝ) (hα : ∀ N, 1 ≤ α N) (hQ : ∀ N, 1 ≤ Q N)
    (hαo : Tendsto (fun N : ℕ => α N / (N : ℝ) ^ ((1 : ℝ) / 2)) atTop (𝓝 0))
    (hQo : Tendsto (fun N : ℕ => Q N ^ 2 * α N ^ 3 * Real.logb 2 N ^ 3 / (N : ℝ) ^ 3)
      atTop (𝓝 0)) :
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : RandAlg N ℝ,
      (∀ G : AdjList N, 2 / 3 ≤ A.prob G (fun muhat =>
        (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α N ≤ muhat ∧
          muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
      ∀ q : ℝ, DistinctCostLE A q → c * Q N ≤ q) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : RandAlg N ℝ,
      (∀ G : AdjList N, 2 / 3 ≤ A.prob G (fun muhat =>
        (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / (N : ℝ) ^ δ ≤ muhat ∧
          muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
      ∀ q : ℝ, DistinctCostLE A q →
        c * ((N : ℝ) ^ ((3 : ℝ) / 2 - 3 / 2 * δ) / Real.logb 2 N ^ 2) ≤ q) := by sorry

end NAMatchEst.Supplement
