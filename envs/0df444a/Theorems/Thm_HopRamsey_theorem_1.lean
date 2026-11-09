-- Prove2me | Theorems.Thm_HopRamsey_theorem_1
-- name    : HopRamsey.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:39.099202+00:00
-- url     : https://prove2.me/theorems/80a10973-e611-4c13-8038-cdf09e0a7c3a
-- title:
--   Theorem 1 (Main): hop-constrained Ramsey-type HST embeddings, exclusion $\varepsilon$, distortion and hop-stretch $\tilde O(\log n)/\varepsilon$, expected distortion $\tilde O(\log n)$
-- statement:
--   For every exponent $c$ there are constants $C>0$ and $K$ such that the following holds. Let $G=(V,E,w)$ be a graph on $n\ge1$ vertices whose edge weights are polynomially related, $w(e)\le n^c\,w(e')$ for all edges $e,e'$; let $h\in\{1,\dots,n\}$ and $\varepsilon\in(0,1)$. Write $\Lambda=\Lambda_K(n)=\log_2(n+1)(1+\log_2(1+\log_2(n+1)))^K$. Then there is a finitely supported distribution $\mathcal D$ over pairs $(U,M)$, where $U$ is an HST whose leaves are all the vertices of $V$ and $M\subseteq V$, and a natural number $\beta\le C\Lambda/\varepsilon$, such that
--
--   1. (**hop-stretch** $\beta$) $d^{(\beta h)}_G(u,v)\le d_U(u,v)$ for every $(U,M)$ in the support and all $u,v\in V$;
--   2. (**distortion**) $d_U(u,v)\le\frac{C\Lambda}{\varepsilon}\,d^{(h)}_G(u,v)$ for every $(U,M)$ in the support, every $u\in M$ and every $v\in V$;
--   3. (**exclusion**) $\Pr[v\notin M]\le\varepsilon$ for every $v\in V$;
--   4. (**expected distortion**) $\mathbb E[d_{U,M}(u,v)]\le C\Lambda\cdot d^{(h)}_G(u,v)$ for all $u,v\in V$, where $d_{U,M}(u,v)=d_U(u,v)$ if $u,v\in M$ and $0$ otherwise.
--
--   That is, there is a stochastic hop-constrained Ramsey-type embedding into HSTs with hop parameter $h$, exclusion probability $\varepsilon$, distortion and hop-stretch $\varepsilon^{-1}\tilde O(\log n)$, and expected distortion $\tilde O(\log n)$. The expected distortion does not degrade with $\varepsilon$, which is the improvement over earlier constructions and what applications with polynomially small $\varepsilon$ need.
--
--   Differences from the source:
--   - reading: "polynomial weights" (all weights finite positive polynomial numbers, minimum 1, p.12) → for a fixed exponent c, w(e) ≤ n^c·w(e′) for all edges e, e′, with C and K allowed to depend on c; reason: "polynomial" fixes the exponent; all four properties scale with the weights, so the ratio form is the scale-free form of weights in [1, n^c]
--   - generalization: weights in [1, n^c] → every graph whose max/min edge-weight ratio is at most n^c, at any scale; reason: every graph with weights in [1, n^c] satisfies the ratio condition
--   - reading: ε^{−1}·Õ(log n) and Õ(log n) → ≤ C·Λ_K(n)/ε and ≤ C·Λ_K(n), with C > 0 and K chosen before the graph, h and ε; reason: the paper's Õ(g) = O(g)·polylog(g) (p.12) with absolute constants; the shifts in Λ_K only keep it ≥ 1 at n = 1, 2
--   - encoding: a distribution over pairs (f, M), f a map into an HST (X, d_X) → a `PMF` on pairs (`ARTreeCover.HST V` with leaf set V, finite saved set); d_X(f(u), f(v)) is the HST's leaf ultrametric at (u, v); reason: every property of Definition 2 reads only the pulled-back distances, and leaf ultrametrics with values in [0,∞] are exactly the HST metrics (p.12)
--   - generalization: a distribution → a distribution with finite support; reason: a stronger conclusion; it implies the printed one
--   - reading: hop-stretch ε^{−1}·Õ(log n) → a natural number β ≤ C·Λ_K(n)/ε; reason: d^{(β·h)} is defined for integer hop counts; smaller β is stronger
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Theorem 1 (Main), p.3 (PDF p.5), restated p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding
import Definitions.Def_HopRamsey_polylogBound

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Theorem 1 (Main), p.3 (PDF p.5), restated p.14 (PDF p.16): "Consider an n-vertex graph
G = (V,E,w) with polynomial weights, and parameters h ∈ [n], ε ∈ (0,1). Then there is a stochastic
hop-constrained Ramsey-type embedding into HSTs with hop parameter h, exclusion probability ε,
distortion ε^{−1}·Õ(log n), hop-stretch ε^{−1}·Õ(log n), and expected distortion Õ(log n)."

**Formalization Note.**
1. Polynomial weights: for an exponent `c`, every edge weight is at most `n^c` times every other
   (the ratio form of "weights in `[1, n^c]`"; all four properties are invariant under scaling the
   weights). The constants `C > 0` and `K` may depend on `c` only and are chosen before the graph.
2. `Õ(log n)` is `C·Λ_K(n)` (`polylogBound`); the hop-stretch is a natural number
   `β ≤ C·Λ_K(n)/ε`.
3. The embedding is one finitely supported `PMF` over pairs (HST with leaf set `V`, saved set)
   with all four properties at once (`IsStochRamseyEmbedding`).
4. Every `ε ∈ (0, 1)` is covered, including `ε ≤ n⁻²` (footnote 8, p.25). -/
theorem theorem_1 :
    ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (h : ℕ) (ε : ℝ),
        1 ≤ Fintype.card V →
        (∀ e ∈ G.graph.edgeSet, ∀ e' ∈ G.graph.edgeSet,
          G.w e ≤ (Fintype.card V : ℝ) ^ c * G.w e') →
        1 ≤ h → h ≤ Fintype.card V → 0 < ε → ε < 1 →
        ∃ D : PMF (HST V × Finset V), D.support.Finite ∧
          (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
          ∃ β : ℕ, (β : ℝ) ≤ C * polylogBound K (Fintype.card V) / ε ∧
            IsStochRamseyEmbedding G h D β (C * polylogBound K (Fintype.card V) / ε) ε
              (C * polylogBound K (Fintype.card V)) := by sorry

end HopRamsey
