-- Prove2me | Theorems.Thm_GirthBethe_Sharp_permutation_estimate
-- name    : GirthBethe.Sharp.permutation_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:19:59.4122+00:00
-- url     : https://prove2.me/theorems/9ed6252a-1e4c-4e5a-8c36-3baccac4329c
-- title:
--   Proposition 3.5 — permutation estimate
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite bipartite graph and $\mu$ a probability law on its perfect matchings, with edge marginals $p$. Let $Z_v$ be the matched neighbour of $v\in V$, identified with an edge at $v$, so that $\mathcal L(Z_v)=p_v$. Then
--   $$\sum_{u\in L}\sum_{v\in V}I_\Gamma(Z_v;X_u)\ \ge\ 2\sum_{u\in L}S(p_u).$$
--
--   Together with the girth estimate it shows $\sum_u\mathrm{gap}(u)\ge0$.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - encoding: conditional laws L(· | X_u = w) and marginals p^{X_u = w} → for P(X_u = w) = 0 the unconditional law is used as the conditional-law version; reason: such terms enter only with weight P(X_u = w) = 0, so no value changes
--   - generalization: the standing setting of §3: even g ≥ 4 and G of girth at least g → no hypothesis on g or on the girth of G; reason: the proof uses only that X is a bijection (§5: the graph plays no role); adding the standing hypotheses gives the source statement
--   - encoding: Γ(L(Z_v)) with Z_v valued in the neighbours of v → Z_v valued in the edges at v, so Γ acts on the local vector p_v; reason: the source makes the same identification
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 10, Proposition 3.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

/-- Proposition 3.5 (permutation estimate): `∑_{u ∈ L} ∑_{v ∈ V} I_Γ(Z_v; X_u) ≥ 2 ∑_{u ∈ L} S(p_u)`. -/
theorem permutation_estimate {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) :
    2 * ∑ u : L, localBethe (localVec (edgeMarg μ) (Sum.inl u)) ≤
      ∑ u : L, ∑ v : L ⊕ R, infoGain gammaFun μ (matchZ v) (matchX u) := by sorry

end GirthBethe.Sharp
