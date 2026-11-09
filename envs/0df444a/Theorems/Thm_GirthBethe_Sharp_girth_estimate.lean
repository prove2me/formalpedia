-- Prove2me | Theorems.Thm_GirthBethe_Sharp_girth_estimate
-- name    : GirthBethe.Sharp.girth_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:19:57.219219+00:00
-- url     : https://prove2.me/theorems/5b551a07-e3f2-4726-b52f-a99e83198a14
-- title:
--   Proposition 3.4 — girth estimate
-- statement:
--   Let $g\ge4$ be even, let $G=(L\sqcup R,E)$ be a finite bipartite graph of girth at least $g$, and let $\mu$ be a probability law on its perfect matchings, with edge marginals $p$ and conditional marginals $p^{X_u}$. Then for every $u\in L$,
--   $$\Phi_0(p)-\mathbb E_{X_u}\Phi_0(p^{X_u})-H(X_u)\ \ge\ -\frac2g\,S(p_u),$$
--   where $\Phi_0$ is (3.5), $\mathbb E_{X_u}\Phi_0(p^{X_u})=\sum_w P(X_u=w)\Phi_0(p^{X_u=w})$ and $H(X_u)$ is the entropy of the law of $X_u$.
--
--   Together with the permutation estimate it shows that a good vertex exists.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: girth at least g, forests having infinite girth → (g : ℕ∞) ≤ (toGraph E).egirth; reason: SimpleGraph.egirth is the length of a shortest cycle and ⊤ for an acyclic graph
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - encoding: conditional laws L(· | X_u = w) and marginals p^{X_u = w} → for P(X_u = w) = 0 the unconditional law is used as the conditional-law version; reason: such terms enter only with weight P(X_u = w) = 0, so no value changes
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 10, Proposition 3.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

/-- Proposition 3.4 (girth estimate): `Φ₀(p) - E_{X_u} Φ₀(p^{X_u}) - H(X_u) ≥ -(2/g) S(p_u)` for every `u ∈ L`. -/
theorem girth_estimate {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (g : ℕ) (hg : Even g) (hg4 : 4 ≤ g) (hgirth : (g : ℕ∞) ≤ (toGraph E).egirth)
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) (u : L) :
    -(2 / (g : ℝ)) * localBethe (localVec (edgeMarg μ) (Sum.inl u)) ≤
      phi0 g E (edgeMarg μ) - ∑ w, law μ (matchX u) w * phi0 g E (condMarg μ u w) -
        shannon (law μ (matchX u)) := by sorry

end GirthBethe.Sharp
