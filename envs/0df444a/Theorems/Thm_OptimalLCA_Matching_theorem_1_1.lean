-- Prove2me | Theorems.Thm_OptimalLCA_Matching_theorem_1_1
-- name    : OptimalLCA.Matching.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:00.758341+00:00
-- url     : https://prove2.me/theorems/80ce99b1-0ddf-48b8-abcf-bca9f55fd805
-- title:
--   Theorem 1.1 — a (1−ε)-approximate matching LCA and an εn-additive estimator with (2Δ)^{O(1/ε)} queries and work per answer
-- statement:
--   There is an absolute constant $C>0$ such that for all $n\ge2$, integers $\Delta\ge2$ and $0<\varepsilon<\tfrac12$:
--
--   **(a)** There is a single randomized LCA program (depending only on $n,\Delta,\varepsilon$; not on $G$, nor on whether $G$ is bipartite) such that for every graph $G$ on $n$ vertices with maximum degree at most $\Delta$, given as adjacency lists in any order, and every realization $\omega$ of the shared random tape:
--   - every mate query and every edge query halts after at most $(2\Delta)^{C/\varepsilon}$ units of work and $(2\Delta)^{C/\varepsilon}$ graph queries;
--   - the edge answers $f_\omega$ form a half-integral fractional matching of $G$;
--   - if $G$ is bipartite, $f_\omega$ is $\{0,1\}$-valued and the mate answers are exactly the matching $M_\omega=\{e:f_\omega(e)=1\}$;
--
--   and
--   $$\Pr_\omega\Big[\textstyle\sum_ef_\omega(e)<(1-\varepsilon)\nu_f(G)\Big]\le\tfrac1{10},\qquad G\text{ bipartite}:\ \Pr_\omega\big[|M_\omega|<(1-\varepsilon)\nu(G)\big]\le\tfrac1{10}.$$
--
--   **(b)** For every $0<\zeta<\tfrac12$ there is an estimator program (depending only on $n,\Delta,\varepsilon,\zeta$) such that for every such $G$ every execution halts after at most $(2\Delta)^{C/\varepsilon}\log(2/\zeta)$ work and graph queries, and
--   $$\Pr\big[|\hat\nu-\nu_f(G)|>\varepsilon n\big]\le\zeta,\qquad G\text{ bipartite}:\ \Pr\big[|\hat\nu-\nu(G)|>\varepsilon n\big]\le\zeta.$$
--
--   Work is counted in the exact-real model of §2.1: every arithmetic operation, comparison, rounding, elementary-function evaluation, uniform draw and graph query is one unit. Feasibility and consistency hold for every tape and every query order; only the approximation guarantees are probabilistic.
--
--   Differences from the source:
--   - reading: (2Δ)^{O(1/ε)} graph queries; (2Δ)^{O(1/ε)} log(2/ζ); the same bounds for computational work → one absolute C > 0 fixed before n, Δ, ε, ζ: per-answer work and queries ≤ (2Δ)^{C/ε}; estimator work and queries ≤ (2Δ)^{C/ε}·log(2/ζ) (natural log); reason: explicit reading of the O(·) as an absolute constant, as the theorem's 'absolute'/'worst case' wording requires
--   - reading: the model of Section 2.1 → the extended real RAM: every executed instruction is one unit of work, degree and neighbour instructions are one graph query each; reason: the unit-cost list of §2.1
--   - encoding: randomized LCA with shared randomness, consistent in every (adaptive) query order → each query is a fresh run of one program on the same tape ω : ℤ → [0,1] (i.i.d. uniform, Measure.infinitePi) with only the query in memory; reason: answers are functions of (G, ω, query), hence consistent in every order
--   - encoding: mate and edge queries; ⊥ → mate query memory (0, v), edge query memory (1, u, v); a mate answer is u.val or −1 for ⊥; edge answers on uv and vu agree; reason: machine input/output conventions
--   - reading: on bipartite graphs, mate queries to a matching M → M_ω = {e : f_ω(e) = 1}; each mate answer is the partner in M_ω or −1; reason: §9.2: 'Both query interfaces access the same projected output'
--   - encoding: probability at least 0.9; at least 1 − ζ → the outer measure of the failure set is ≤ 1/10; ≤ ζ; reason: no measurability assumption on the failure events
--   - encoding: vertices labelled [n]; adjacency lists in a fixed arbitrary order → Fin n with vertex v the integer v.val; AdjLists (Fin n), ∀ lists; reason: relabelling; every neighbour order is quantified
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 3–4, Theorem 1.1 (proved in §8, p. 42, and §9.3, p. 45)

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_Machine

namespace OptimalLCA.Matching

/-- Theorem 1.1 (randomized local computation and estimation). There is an absolute
constant `C` such that for all `n ≥ 2`, integers `Δ ≥ 2` and `0 < ε < 1/2`:
(a) one LCA program answers mate and edge queries on every graph on `Fin n` of maximum
degree `≤ Δ`, given as adjacency lists in any order, with at most `(2Δ)^{C/ε}` work and
graph queries per answer for every tape; its edge answers form a half-integral fractional
matching (integral on bipartite graphs, where the mate answers are exactly the matching
`{e : f e = 1}`); the value falls below `(1-ε) ν_f(G)` (on bipartite graphs the matching
size below `(1-ε) ν(G)`) with outer probability at most `1/10`;
(b) for every `0 < ζ < 1/2` one estimator program uses at most `(2Δ)^{C/ε} log(2/ζ)` work
and graph queries on every tape and errs by more than `εn` with outer probability `≤ ζ`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ Δ : ℕ, 2 ≤ Δ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (∃ P : Program, ∀ A : AdjLists (Fin n), A.MaxDegLE Δ →
        (∀ ω : ℤ → unitInterval,
          (∀ v : Fin n, HaltsWithin P (graphEnv A (tapeReal ω)) (mateInput v)
              ((2 * (Δ : ℝ)) ^ (C / ε))) ∧
          (∀ u v : Fin n, A.toGraph.Adj u v →
              HaltsWithin P (graphEnv A (tapeReal ω)) (edgeInput u v)
                ((2 * (Δ : ℝ)) ^ (C / ε))) ∧
          (∀ u v : Fin n, A.toGraph.Adj u v → edgeAnswer P A ω u v = edgeAnswer P A ω v u) ∧
          IsFracMatching A.toGraph (lcaEdgeFn P A ω) ∧
          IsHalfIntegral A.toGraph (lcaEdgeFn P A ω) ∧
          (MatousekLP.Integrality.IsBipartite A.toGraph →
            (∀ e ∈ A.toGraph.edgeFinset, lcaEdgeFn P A ω e = 0 ∨ lcaEdgeFn P A ω e = 1) ∧
            ∀ v : Fin n,
              (mateAnswer P A ω v = -1 ∧
                  ∀ u : Fin n, A.toGraph.Adj v u → lcaEdgeFn P A ω s(v, u) ≠ 1) ∨
                ∃ u : Fin n, A.toGraph.Adj v u ∧ lcaEdgeFn P A ω s(v, u) = 1 ∧
                  mateAnswer P A ω v = (u.val : ℝ))) ∧
        tapeMeasure {ω | fracValue A.toGraph (lcaEdgeFn P A ω) <
            (1 - ε) * fracMatchingNumber A.toGraph} ≤ 1 / 10 ∧
        (MatousekLP.Integrality.IsBipartite A.toGraph →
          tapeMeasure {ω |
            (((A.toGraph.edgeFinset.filter (fun e => lcaEdgeFn P A ω e = 1)).card : ℕ) : ℝ) <
              (1 - ε) * (matchingNumber A.toGraph : ℝ)} ≤ 1 / 10)) ∧
      (∀ ζ : ℝ, 0 < ζ → ζ < 1 / 2 →
        ∃ E : Program, ∀ A : AdjLists (Fin n), A.MaxDegLE Δ →
          (∀ ω : ℤ → unitInterval, HaltsWithin E (graphEnv A (tapeReal ω)) (fun _ => 0)
              ((2 * (Δ : ℝ)) ^ (C / ε) * Real.log (2 / ζ))) ∧
          tapeMeasure {ω | ε * (n : ℝ) <
              |estimate E A ω - fracMatchingNumber A.toGraph|} ≤ ENNReal.ofReal ζ ∧
          (MatousekLP.Integrality.IsBipartite A.toGraph →
            tapeMeasure {ω | ε * (n : ℝ) <
              |estimate E A ω - (matchingNumber A.toGraph : ℝ)|} ≤ ENNReal.ofReal ζ)) := by sorry

end OptimalLCA.Matching
