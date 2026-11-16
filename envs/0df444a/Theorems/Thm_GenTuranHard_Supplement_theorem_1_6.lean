-- Prove2me | Theorems.Thm_GenTuranHard_Supplement_theorem_1_6
-- name    : GenTuranHard.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:09.562164+00:00
-- url     : https://prove2.me/theorems/91685345-345a-4100-8743-6ea1c09a3a3b
-- title:
--   Theorem 1.6 — for complete multipartite $T = K_{s_1,\dots,s_r}$, $r \ge 3$, approximating $\mathrm{ex}$ and $\mathrm{ex}^\prime$ within $n^{v(T)-\varepsilon}$ is NP-hard
-- statement:
--   Let $T = K_{s_1,\dots,s_r}$ be the complete $r$-partite graph with partite sets of sizes $s_1, \dots, s_r$, where $r \ge 3$ and $s_1, \dots, s_r \ge 1$. Let $\mathcal F$ be a nonempty family of graphs such that no $F \in \mathcal F$ is a subgraph of a blow-up of $T$, and let $\varepsilon > 0$. Then for each of the two parameters $\mathrm{ex}(G, T, \mathcal F)$ and $\mathrm{ex}'(G, T, \mathcal F)$, approximation within an additive error of
--
--   $$
--   n^{v(T) - \varepsilon}
--   $$
--
--   is NP-hard for an input graph $G$ on $n$ vertices.
--
--   Together with Theorem 1.5 (which covers $r \le 2$, the bipartite case), this confirms the Alon–Shikhelman conjecture (Conjecture 1.4) for every complete multipartite counted graph $T$, in particular for every clique $T = K_m$.
--
--   **Formalization Note** $T$, $\mathcal F$ and $\varepsilon$ are fixed; only the host graph $G$ is the input, and every host graph is admissible. $\mathcal F$ may be finite or infinite. NP-hardness is the mission's one-query notion (the same as in the goal, Theorem 1.5). $K_{s_1,\dots,s_r}$ is Mathlib's complete multipartite graph on the vertex type $\Sigma_{i<r}\{0,\dots,s_i-1\}$, so $v(T) = s_1 + \dots + s_r$. The hypothesis on $\mathcal F$ is stated through blow-ups, as printed.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: a family F of graphs, finite or infinite → a set of finite graphs on Fin m (FinGraph); reason: every finite graph is isomorphic to one on {0,…,m−1}; F-freeness is isomorphism-invariant
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
--   - encoding: “F is a subgraph of a blow-up of T” → F has a copy in blowUp T s for some s with all cluster sizes positive; reason: the paper's definition (pp.3, 5)
--   - encoding: T = K_{s1,…,sr}, the complete r-partite graph with partite sets of sizes s1,…,sr → Mathlib completeMultipartiteGraph with parts Fin (s i), on Σ i : Fin r, Fin (s i); reason: vertices (i, j) adjacent iff their part indices differ; v(T) = Σ s_i is the cardinality of the vertex type
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Theorem 1.6, p.3 (proof §5.3, pp.26–30)

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_blowUp
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

namespace Supplement

/-- **Theorem 1.6** (Chen, He, Li, Ma, Xie, *NP-hardness of additive approximation for generalized
Turán problems*, arXiv:2610.16358, sha256 dc85633a…, Theorem 1.6, p.3). Let `T = K_{s₁,…,s_r}` with
`r ≥ 3` and `s₁, …, s_r ≥ 1`, `𝓕` a nonempty family such that no `F ∈ 𝓕` is a subgraph of a blow-up
of `T`, and `ε > 0`. Then for each of `ex(G, T, 𝓕)` and `ex′(G, T, 𝓕)`, approximation within an
additive error of `n^{v(T)−ε}` is NP-hard for an input graph `G` on `n` vertices.

**Formalization Note** `K_{s₁,…,s_r}` is Mathlib's `completeMultipartiteGraph` with parts
`Fin (s i)`, on the vertex type `W = Σ i : Fin r, Fin (s i)`, so `v(T) = Σ s_i = Fintype.card W`.
NP-hardness is the published one-query notion `AddApproxNPHard` with `Dom = True` (every host graph
is an input), exactly as in the base goal `GenTuranHard.theorem_1_5`; "for each of the two parameters" is
the conjunction of the `exT` and the `exSpan` statements. `𝓕` (`Fam : Set FinGraph`) may be finite or
infinite. The error is `(n : ℝ) ^ ((v(T) : ℝ) − ε)` (`Real.rpow`), every `ε > 0` allowed. -/
theorem theorem_1_6 (r : ℕ) (hr : 3 ≤ r) (s : Fin r → ℕ) (hs : ∀ i, 1 ≤ s i)
    (Fam : Set FinGraph) (hFne : Fam.Nonempty)
    (hF : ∀ F ∈ Fam, ¬ InBlowUp F.2
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin r => Fin (s i))))
    (ε : ℝ) (hε : 0 < ε) :
    AddApproxNPHard encGraph (fun _ => True)
        (fun G => (exT G.2 (SimpleGraph.completeMultipartiteGraph (fun i : Fin r => Fin (s i))) Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card (Σ i : Fin r, Fin (s i)) : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun _ => True)
        (fun G => (exSpan G.2 (SimpleGraph.completeMultipartiteGraph (fun i : Fin r => Fin (s i))) Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card (Σ i : Fin r, Fin (s i)) : ℝ) - ε)) := by sorry

end Supplement

end GenTuranHard
