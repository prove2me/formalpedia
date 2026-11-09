-- Prove2me | Theorems.Thm_GirthBethe_Sharp_matching_entropy_girth_bound
-- name    : GirthBethe.Sharp.matching_entropy_girth_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:09.185259+00:00
-- url     : https://prove2.me/theorems/6445f59c-69cc-4cfc-9872-fab5f40f3ba1
-- title:
--   Theorem 3.1 — $H(\mu)\le\Phi_G(p)$ for graphs of girth at least $g$
-- statement:
--   Let $g\ge4$ be even and let $G=(L\sqcup R,E)$ be a finite bipartite graph of girth at least $g$ with $|L|=|R|=n$. Let $\mu$ be any probability distribution on the perfect matchings of $G$, with edge marginals $p_e=P_{M\sim\mu}(e\in M)$. Then
--   $$H(\mu)\le\Phi_G(p)=H_B(p)+\frac2g\sum_{v\in V}F(p_v),$$
--   equivalently
--   $$H(\mu)-H_B(p)\le\frac2g\sum_{v\in V}F(p_v).$$
--
--   This is the paper's main entropy inequality; with Propositions 2.4 and 2.10 it gives the upper bound of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: girth at least g, forests having infinite girth → (g : ℕ∞) ≤ (toGraph E).egirth; reason: SimpleGraph.egirth is the length of a shortest cycle and ⊤ for an acyclic graph
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - encoding: F(p_v) with π uniform on Sym(d_v), p_v = (p_e)_{e ∋ v} → anariRezaei (localVec p v): the local vector is indexed by the incident edges and π is uniform over all orderings Fin d_v ≃ {e ∋ v}; reason: F is invariant under relabelling the coordinates, so this is F of p_v ∈ Δ_{d_v}
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 9, Theorem 3.1 (with the standing assumption 'Fix an even integer g ≥ 4', p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

/-- Theorem 3.1: `H(μ) ≤ Φ_G(p)`, equivalently `H(μ) - H_B(p) ≤ (2/g) ∑_v F(p_v)`. -/
theorem matching_entropy_girth_bound {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (g : ℕ) (hg : Even g) (hg4 : 4 ≤ g) (hgirth : (g : ℕ∞) ≤ (toGraph E).egirth)
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) :
    shannon μ ≤ phi g E (edgeMarg μ) ∧
      shannon μ - betheEntropy E (edgeMarg μ) ≤
        (2 / (g : ℝ)) * ∑ v : L ⊕ R, anariRezaei (localVec (edgeMarg μ) v) := by sorry

end GirthBethe.Sharp
