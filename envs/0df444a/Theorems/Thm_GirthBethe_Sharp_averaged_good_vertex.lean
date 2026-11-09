-- Prove2me | Theorems.Thm_GirthBethe_Sharp_averaged_good_vertex
-- name    : GirthBethe.Sharp.averaged_good_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:22.624208+00:00
-- url     : https://prove2.me/theorems/963efabe-a875-45cb-875c-eef05bcef7ad
-- title:
--   Proposition 3.3 — $\sum_u\mathrm{gap}(u)\ge0$; a good vertex exists
-- statement:
--   Let $g\ge4$ be even, let $G=(L\sqcup R,E)$ be a finite bipartite graph of girth at least $g$ with $|L|=|R|=n\ge1$, and let $\mu$ be a probability law on its perfect matchings. With $p$, $p^{X_u}$ and $\mathrm{gap}(u)$ as in (3.2)–(3.4),
--   $$\sum_{u\in L}\mathrm{gap}(u)\ \ge\ 0,$$
--   and in particular there exists a good vertex $u\in L$, i.e. $\mathrm{gap}(u)\ge0$.
--
--   The good vertex is the inductive step of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: girth at least g, forests having infinite girth → (g : ℕ∞) ≤ (toGraph E).egirth; reason: SimpleGraph.egirth is the length of a shortest cycle and ⊤ for an acyclic graph
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - encoding: conditional laws L(· | X_u = w) and marginals p^{X_u = w} → for P(X_u = w) = 0 the unconditional law is used as the conditional-law version; reason: such terms enter only with weight P(X_u = w) = 0, so no value changes
--   - encoding: F(p_v) with π uniform on Sym(d_v), p_v = (p_e)_{e ∋ v} → anariRezaei (localVec p v): the local vector is indexed by the incident edges and π is uniform over all orderings Fin d_v ≃ {e ∋ v}; reason: F is invariant under relabelling the coordinates, so this is F of p_v ∈ Δ_{d_v}
--   - encoding: n ≥ 1 → 1 ≤ Fintype.card L; reason: the same condition (|R| = |L| is forced by the existence of μ)
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 10, Proposition 3.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

/-- Proposition 3.3: `∑_{u ∈ L} gap(u) ≥ 0`; in particular a good vertex exists. -/
theorem averaged_good_vertex {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (g : ℕ) (hg : Even g) (hg4 : 4 ≤ g) (hgirth : (g : ℕ∞) ≤ (toGraph E).egirth)
    (hn : 1 ≤ Fintype.card L)
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) :
    0 ≤ ∑ u, gap g μ u ∧ ∃ u, 0 ≤ gap g μ u := by sorry

end GirthBethe.Sharp
