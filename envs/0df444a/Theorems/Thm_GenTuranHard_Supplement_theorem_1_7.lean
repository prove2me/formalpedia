-- Prove2me | Theorems.Thm_GenTuranHard_Supplement_theorem_1_7
-- name    : GenTuranHard.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:57.653437+00:00
-- url     : https://prove2.me/theorems/2022454f-83ad-49be-b793-f2fb91a9ae4d
-- title:
--   Theorem 1.7 — if every $F \in \mathcal F$ has $\chi(F) \ge \chi(T)+2$, approximating $\mathrm{ex}$ and $\mathrm{ex}^\prime$ within $n^{v(T)-\varepsilon}$ is NP-hard
-- statement:
--   Let $T$ be a graph with $e(T) > 0$, let $\mathcal F$ be a nonempty family of graphs with
--
--   $$
--   \min_{F \in \mathcal F} \chi(F) \ge \chi(T) + 2,
--   $$
--
--   and let $\varepsilon > 0$. Then for each of the two parameters $\mathrm{ex}(G, T, \mathcal F)$ and $\mathrm{ex}'(G, T, \mathcal F)$, approximation within an additive error of
--
--   $$
--   n^{v(T) - \varepsilon}
--   $$
--
--   is NP-hard for an input graph $G$ on $n$ vertices.
--
--   This confirms the Alon–Shikhelman conjecture (Conjecture 1.4) whenever every forbidden graph has chromatic number at least $\chi(T)+2$; no structural restriction is placed on $T$ beyond having an edge. (A graph with $\chi(F) \ge \chi(T)+2$ is not a subgraph of a blow-up of $T$, so the hypothesis of the conjecture holds.)
--
--   **Formalization Note** $T$, $\mathcal F$ and $\varepsilon$ are fixed; only the host graph $G$ is the input, and every host graph is admissible. $\mathcal F$ may be finite or infinite. NP-hardness is the mission's one-query notion (the same as in the goal, Theorem 1.5). Chromatic numbers are Mathlib's, valued in $\mathbb N\cup\{\infty\}$; they are finite for finite graphs. $T = K_2$ and graphs $T$ with isolated vertices are included.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: a family F of graphs, finite or infinite → a set of finite graphs on Fin m (FinGraph); reason: every finite graph is isomorphic to one on {0,…,m−1}; F-freeness is isomorphism-invariant
--   - encoding: n^{v(T)−ε} → (n : ℝ) ^ ((v(T) : ℝ) − ε) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
--   - encoding: min_{F∈𝓕} χ(F) ≥ χ(T) + 2 → ∀ F ∈ 𝓕, T.chromaticNumber + 2 ≤ F.chromaticNumber (in ℕ∞); reason: the minimum of a nonempty set of naturals is ≥ c iff every member is ≥ c; the chromatic number of a finite graph is finite
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Theorem 1.7, p.4 (derived from Theorem 5.1, p.22)

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

namespace Supplement

/-- **Theorem 1.7** (Chen, He, Li, Ma, Xie, *NP-hardness of additive approximation for generalized
Turán problems*, arXiv:2610.16358, sha256 dc85633a…, Theorem 1.7, p.4). Let `T` be a graph with
`e(T) > 0`, `𝓕` a nonempty family of graphs with `min_{F∈𝓕} χ(F) ≥ χ(T) + 2`, and `ε > 0`. Then for
each of `ex(G, T, 𝓕)` and `ex′(G, T, 𝓕)`, approximation within an additive error of `n^{v(T)−ε}` is
NP-hard for an input graph `G` on `n` vertices.

**Formalization Note** `min_{F∈𝓕} χ(F) ≥ χ(T) + 2` is "every member `F` has
`χ(T) + 2 ≤ χ(F)`", with Mathlib's `chromaticNumber` in `ℕ∞` (finite for finite graphs).
NP-hardness is the published one-query notion `AddApproxNPHard` with `Dom = True` (every host graph
is an input), exactly as in the base goal `GenTuranHard.theorem_1_5`; "for each of the two parameters" is
the conjunction of the `exT` and the `exSpan` statements. `𝓕` (`Fam : Set FinGraph`) may be finite or
infinite. The error is `(n : ℝ) ^ ((v(T) : ℝ) − ε)` (`Real.rpow`), every `ε > 0` allowed. -/
theorem theorem_1_7 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hTe : T.edgeSet.Nonempty)
    (Fam : Set FinGraph) (hFne : Fam.Nonempty)
    (hχ : ∀ F ∈ Fam, T.chromaticNumber + 2 ≤ F.2.chromaticNumber)
    (ε : ℝ) (hε : 0 < ε) :
    AddApproxNPHard encGraph (fun _ => True) (fun G => (exT G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) ∧
      AddApproxNPHard encGraph (fun _ => True) (fun G => (exSpan G.2 T Fam : ℝ))
        (fun G => (G.1 : ℝ) ^ ((Fintype.card W : ℝ) - ε)) := by sorry

end Supplement

end GenTuranHard
