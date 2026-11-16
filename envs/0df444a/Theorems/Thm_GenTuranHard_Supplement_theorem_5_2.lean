-- Prove2me | Theorems.Thm_GenTuranHard_Supplement_theorem_5_2
-- name    : GenTuranHard.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:42:04.828027+00:00
-- url     : https://prove2.me/theorems/910869f3-053f-44b1-b37e-7e1d5d89424e
-- title:
--   Theorem 5.2 — if $\min\chi(F) = k > \omega(T)$ and every $F \in \mathcal F$ contains $K_k$, approximating $\mathrm{ex}$ and $\mathrm{ex}^\prime$ within $n^{v(T)-\varepsilon}$ is NP-hard
-- statement:
--   Let $T$ be a graph with $e(T) > 0$, let $\mathcal F$ be a nonempty family of graphs such that
--
--   $$
--   \min_{F \in \mathcal F} \chi(F) = k > \omega(T)
--   $$
--
--   and every $F \in \mathcal F$ contains $K_k$ as a subgraph, and let $\varepsilon > 0$. Here $\omega(T)$ is the clique number of $T$. Then for each of the two parameters $\mathrm{ex}(G, T, \mathcal F)$ and $\mathrm{ex}'(G, T, \mathcal F)$, approximation within an additive error of
--
--   $$
--   n^{v(T) - \varepsilon}
--   $$
--
--   is NP-hard for an input graph $G$ on $n$ vertices.
--
--   Taking $\mathcal F = \{K_k\}$ gives the Alon–Shikhelman conjecture for $\mathrm{ex}(G, T, K_k)$ for every $T$ with $\omega(T) < k$, extending Theorem 1.3 of [AS22] (the case $T = K_m$, $m < k$) to arbitrary counted graphs.
--
--   **Formalization Note** $T$, $\mathcal F$ and $\varepsilon$ are fixed; only the host graph $G$ is the input, and every host graph is admissible. $\mathcal F$ may be finite or infinite. NP-hardness is the mission's one-query notion (the same as in the goal, Theorem 1.5). "$\min_{F\in\mathcal F}\chi(F) = k$" is stated as: no member of $\mathcal F$ is $(k-1)$-colourable and some member is $k$-colourable. Both hypotheses on $\mathcal F$ are kept, although containing $K_k$ already gives $\chi(F) \ge k$.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: a family F of graphs, finite or infinite → a set of finite graphs on Fin m (FinGraph); reason: every finite graph is isomorphic to one on {0,…,m−1}; F-freeness is isomorphism-invariant
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
--   - encoding: min_{F∈𝓕} χ(F) = k → no member of 𝓕 is (k−1)-colourable, and some member is k-colourable; reason: chromatic numbers are natural numbers, so the minimum over a nonempty family exists; this is the convention of the published Corollary 3.3
--   - encoding: k > ω(T) → T.CliqueFree k; reason: ω(T) < k iff T has no clique of order k
--   - encoding: F contains K_k as a subgraph → (cliqueFG k).2 ⊑ F.2: the complete graph on Fin k has a copy (injective homomorphism) in F; reason: "subgraph" in the paper's not-necessarily-induced sense
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Theorem 5.2, p.22 (proof §5.2, p.26)

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

namespace Supplement

/-- **Theorem 5.2** (Chen, He, Li, Ma, Xie, *NP-hardness of additive approximation for generalized
Turán problems*, arXiv:2610.16358, sha256 dc85633a…, Theorem 5.2, p.22). Let `T` be a graph with
`e(T) > 0`, `𝓕` a nonempty family of graphs such that `min_{F∈𝓕} χ(F) = k > ω(T)` and every `F ∈ 𝓕`
contains `K_k` as a subgraph, and `ε > 0`. Then for each of `ex(G, T, 𝓕)` and `ex′(G, T, 𝓕)`,
approximation within an additive error of `n^{v(T)−ε}` is NP-hard for an input graph `G` on `n`
vertices.

**Formalization Note** `min_{F∈𝓕} χ(F) = k` is encoded as in the published `corollary_3_3` (no
member `(k−1)`-colourable, some member `k`-colourable); `k > ω(T)` is `T.CliqueFree k` (no clique of
order `k` in `T`); "`F` contains `K_k`" is `(cliqueFG k).2 ⊑ F.2`, i.e. the complete graph on
`Fin k` has a copy in `F`. NP-hardness is the published one-query notion `AddApproxNPHard` with `Dom = True` (every host graph
is an input), exactly as in the base goal `GenTuranHard.theorem_1_5`; "for each of the two parameters" is
the conjunction of the `exT` and the `exSpan` statements. `𝓕` (`Fam : Set FinGraph`) may be finite or
infinite. The error is `(n : ℝ) ^ ((v(T) : ℝ) − ε)` (`Real.rpow`), every `ε > 0` allowed. -/
theorem theorem_5_2 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hTe : T.edgeSet.Nonempty)
    (Fam : Set FinGraph) (hFne : Fam.Nonempty)
    (k : ℕ) (hkF : ∀ F ∈ Fam, ¬ F.2.Colorable (k - 1))
    (hkF' : ∃ F ∈ Fam, F.2.Colorable k)
    (hkω : T.CliqueFree k)
    (hKk : ∀ F ∈ Fam, (cliqueFG k).2.IsContained F.2)
    (ε : ℝ) (hε : 0 < ε) :
    AddApproxNPHard encGraph (fun _ => True) (fun G => (exT G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun _ => True) (fun G => (exSpan G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) := by sorry

end Supplement

end GenTuranHard
