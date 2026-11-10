-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_8_1
-- name    : LoadBalMatch.Main.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:34:19.600656+00:00
-- url     : https://prove2.me/theorems/863fb0bc-16cc-4ab3-936e-d125401f3163
-- title:
--   Lemma 8.1 — w.p. $\ge1-n^{-n}$, for every $H\subseteq G$ the edges violating $H\cup R$ carry $p$-mass $\le 5n\ln n$
-- statement:
--   Let $G$ be a graph on the finite set $V$ with $n=|V|$ and edge set $E$. For each $e\in E$ let $p_e\in[0,1]$, and let $R\subseteq E$ include each edge $e$ independently with probability $p_e$. Then with probability at least $1-n^{-n}$ over $R$ the following holds simultaneously for every subgraph $H\subseteq G$: if $x$ is a balanced fractional matching on $H\cup R$ and $F$ is the set of edges of $G$ that violate $x$ (Definition 7.12, for the graph $H\cup R$), then
--   $$\sum_{e\in F}p_e\ \le\ 5n\ln n .$$
--
--   Here $\ln$ is the natural logarithm. The lemma bounds how much probability mass the doubling step of Algorithm 4 can add in one iteration.
--
--   Differences from the source:
--   - reading: F the set of edges in E that violate H ∪ R → for every balanced fractional matching x on H ∪ R, the edges of G violating x; reason: the proof fixes one balanced x; the violating set is stated for every one (loads and levels are unique, Lemma 6.10)
--   - encoding: p_e ∈ [0, 1] for e ∈ E; probability over R → p : Sym2 V → ℝ with 0 ≤ p e ≤ 1 on E; the product law sampleEventProb; reason: same distribution
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 44, Lemma 8.1

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_Violation
import Definitions.Def_LoadBalMatch_Main_Sampling

namespace LoadBalMatch.Main

theorem lemma_8_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (p : Sym2 V → ℝ) (hp : ∀ e ∈ G.edgeSet, 0 ≤ p e ∧ p e ≤ 1) :
    1 - ((Fintype.card V : ℝ) ^ Fintype.card V)⁻¹ ≤
      sampleEventProb G p (fun R => ∀ H : SimpleGraph V, H ≤ G →
        ∀ x : Sym2 V → ℝ, IsBalanced (addEdges H ↑R) x →
          violMass G (addEdges H ↑R) x p ≤
            5 * (Fintype.card V : ℝ) * Real.log (Fintype.card V)) := by sorry

end LoadBalMatch.Main
