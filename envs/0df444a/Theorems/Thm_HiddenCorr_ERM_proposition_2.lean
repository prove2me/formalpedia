-- Prove2me | Theorems.Thm_HiddenCorr_ERM_proposition_2
-- name    : HiddenCorr.ERM.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:14.200502+00:00
-- url     : https://prove2.me/theorems/0db05833-43ef-4f22-bd52-f5cbf1da7dd7
-- title:
--   Proposition 2 — unbiased weights: characterization, unique minimum-norm $w^\star=B^\top L^\dagger u/(u^\top L^\dagger u)$, $\|w^\star\|_2^2=1/n_{\mathrm{eff}}(G)$
-- statement:
--   Let $G$ be a matching-covered bipartite graph with $n\ge1$ vertices on each side (with at least one perfect matching, as throughout the paper), incidence matrix $B$, Laplacian $L$ and demand vector $u$. A vector $w\in\mathbb R^{|E|}$ satisfies
--   $$\langle w,x_{M'}\rangle=1\quad\text{for every }M'\in\mathcal M(G)$$
--   if and only if $w=B^\top z$ for some $z\in\mathbb R^{2n}$ with $\langle z,u\rangle=1$. Among these vectors, the unique minimizer of $\|w\|_2$ is
--   $$w^\star=\frac{B^\top L^\dagger u}{u^\top L^\dagger u},\qquad\text{and}\qquad \|w^\star\|_2^2=\frac1{n_{\mathrm{eff}}(G)}.$$
--
--   The constraints say that the bilinear covariance estimator with weights $w$ is unbiased for every possible hidden matching; $w^\star$ is the variance-optimal choice, and its norm is the origin of the effective sample size.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: matching-covered G (with the standing assumption of §4.1 that M(G) is nonempty) and n vertices on each side → hypotheses MatchingCovered E, ∃ σ, IsPerfectMatching E σ, and 0 < n; reason: the §4.1 standing assumption made explicit; n = 0 is the empty graph, where no w is feasible and w⋆ = 0/0
--   - encoding: the unique minimizer of ‖w‖₂ among the feasible vectors is w⋆ → w⋆ is feasible and every feasible w ≠ w⋆ has ∑ₑ w⋆ₑ² < ∑ₑ wₑ²; reason: definition of a unique minimizer, with squared norms
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 9, Proposition 2, Eq. (11) (restated p. 19; proof p. 20)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open Matrix

namespace HiddenCorr.ERM

/-- **Proposition 2** (unbiased weights), p. 9 (restated p. 19). Let `G` be a matching-covered
bipartite graph with `n ≥ 1` vertices on each side (and, as throughout, at least one perfect
matching). A vector `w ∈ ℝ^{|E|}` satisfies `⟨w, x_{M'}⟩ = 1` for every perfect matching `M'` if and
only if `w = Bᵀ z` for some `z ∈ ℝ^{2n}` with `⟨z, u⟩ = 1`. Among these vectors the unique minimizer
of `‖w‖₂` is `w⋆ = Bᵀ L† u / (uᵀ L† u)`, and `‖w⋆‖₂² = 1 / n_eff(G)`. -/
theorem proposition_2 (n : ℕ) (hn : 0 < n) (E : Finset (Fin n × Fin n))
    (hE : MatchingCovered E) (hPM : ∃ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ) :
    (∀ w : E → ℝ,
        (∀ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ → w ⬝ᵥ matchingIndicator E σ = 1) ↔
          ∃ z : Vtx n → ℝ, w = (incidence E)ᵀ *ᵥ z ∧ z ⬝ᵥ demand n = 1) ∧
      ((∀ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ →
          wStar E ⬝ᵥ matchingIndicator E σ = 1) ∧
        ∀ w : E → ℝ,
          (∀ σ : Equiv.Perm (Fin n), IsPerfectMatching E σ → w ⬝ᵥ matchingIndicator E σ = 1) →
            w ≠ wStar E → ∑ e, wStar E e ^ 2 < ∑ e, w e ^ 2) ∧
      ∑ e, wStar E e ^ 2 = 1 / neff E := by sorry

end HiddenCorr.ERM
