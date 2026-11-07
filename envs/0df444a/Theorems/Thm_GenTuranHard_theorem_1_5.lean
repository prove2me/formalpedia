-- Prove2me | Theorems.Thm_GenTuranHard_theorem_1_5
-- name    : GenTuranHard.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:49.755496+00:00
-- url     : https://prove2.me/theorems/1bf0c4d7-07cf-44c9-8525-7f800154697a
-- title:
--   Theorem 1.5 — for bipartite $T$, approximating $\mathrm{ex}(G,T,\mathcal F)$ and $\mathrm{ex}'(G,T,\mathcal F)$ within $n^{v(T)-\varepsilon}$ is NP-hard
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$, let $\mathcal F$ be a nonempty family of graphs such that no $F \in \mathcal F$ is a subgraph of a blow-up of $T$, and let $\varepsilon > 0$. Then for each of the two parameters $\mathrm{ex}(G, T, \mathcal F)$ and $\mathrm{ex}'(G, T, \mathcal F)$, approximation within an additive error of
--
--   $$
--   n^{v(T) - \varepsilon}
--   $$
--
--   is NP-hard for an input graph $G$ on $n$ vertices.
--
--   This confirms the conjecture of Alon and Shikhelman (Conjecture 1.4) for every bipartite counted graph $T$: by Theorem 1.2 of [AS22], if some member of $\mathcal F$ is a subgraph of a blow-up of $T$, then an additive approximation within $n^{v(T)-\varepsilon(T,\mathcal F)}$ is possible in polynomial time, so the hypothesis on $\mathcal F$ is exactly the condition for hardness at this scale.
--
--   **Formalization Note** $T$, $\mathcal F$ and $\varepsilon$ are fixed; only the host graph $G$ is the input, and every host graph is admissible. $\mathcal F$ may be finite or infinite. The footnote's convention that every member of $\mathcal F$ has an edge is implied by the hypothesis on $\mathcal F$ (an edgeless graph is a subgraph of a blow-up of any graph with a vertex) and is not a separate hypothesis. $T = K_2$ and graphs $T$ with isolated vertices are included.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: a family F of graphs, finite or infinite → a set of finite graphs on Fin m (FinGraph); reason: every finite graph is isomorphic to one on {0,…,m−1}; F-freeness is isomorphism-invariant
--   - encoding: “F is a subgraph of a blow-up of T” → F has a copy in blowUp T s for some s with all cluster sizes positive; reason: the paper's definition (pp.3, 5)
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Theorem 1.5, p.3 (proof §4, pp.12–22)

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_blowUp
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

/-- **Theorem 1.5** (Chen, He, Li, Ma, Xie, *NP-hardness of additive approximation for generalized
Turán problems*, arXiv:2610.16358, sha256 dc85633a…, Theorem 1.5, p.3). Let `T` be a bipartite graph
with `e(T) > 0`, `𝓕` a nonempty family such that no `F ∈ 𝓕` is a subgraph of a blow-up of `T`, and
`ε > 0`. Then for each of `ex(G, T, 𝓕)` and `ex′(G, T, 𝓕)`, approximation within the additive error
`n^{v(T)−ε}` is NP-hard for an input graph `G` on `n` vertices.

**Formalization Note** NP-hardness is the one-query notion `AddApproxNPHard` (for every NP language a
polynomial-time map to host graphs, measured on the graph code `encGraph`, and a polynomial-time answer
map correct for every rational answer within the error). Every host graph is admissible (`Dom = True`).
`𝓕` may be finite or infinite. Footnote 1's "every graph therein has at least one edge" is implied by
`hF` (an edgeless graph is contained in a blow-up of any `T` with a vertex) and is not a hypothesis.
The error is `(n : ℝ) ^ ((v(T) : ℝ) − ε)` (`Real.rpow`) and every `ε > 0` is allowed. -/
theorem theorem_1_5 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hT : T.IsBipartite) (hTe : T.edgeSet.Nonempty)
    (Fam : Set FinGraph) (hFne : Fam.Nonempty) (hF : ∀ F ∈ Fam, ¬ InBlowUp F.2 T)
    (ε : ℝ) (hε : 0 < ε) :
    AddApproxNPHard encGraph (fun _ => True) (fun G => (exT G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun _ => True) (fun G => (exSpan G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) := by sorry

end GenTuranHard
