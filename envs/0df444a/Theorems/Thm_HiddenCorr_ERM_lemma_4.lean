-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_4
-- name    : HiddenCorr.ERM.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:13.907785+00:00
-- url     : https://prove2.me/theorems/17f9a22a-a990-4825-987d-274442e51bc7
-- title:
--   Lemma 4 — vector-valued contraction: $\hat{\mathfrak R}^{\mathrm{vec}}_X(\phi\circ F)\le\sqrt2L\,\hat{\mathfrak R}^{\mathrm{multi}}_X(F)+B_\phi$
-- statement:
--   Let $F$ be a nonempty class of functions $\mathcal X\to\mathbb R^k$ with values in $\mathcal Z$, let $\phi:\mathcal Z\to\mathbb R^{k'}$ be $L$-Lipschitz for some $k'\ge1$, and let $X=(X_1,\dots,X_n)$ be a sample with $\sup_{f\in F}\max_i\|\phi(f(X_i))\|_2\le B_\phi$. With
--   $$\hat{\mathfrak R}^{\mathrm{multi}}_X(F)=\sup_{\|\alpha\|_2\le1}\mathbb E_\varepsilon\sup_{f\in F}\sum_{i=1}^n\sum_{r=1}^k\varepsilon_{ir}\alpha_if_r(X_i)$$
--   ($\varepsilon_{ir}$ i.i.d. unbiased Rademacher signs),
--   $$\hat{\mathfrak R}^{\mathrm{vec}}_X(\phi\circ F)\le\sqrt2\,L\,\hat{\mathfrak R}^{\mathrm{multi}}_X(F)+B_\phi.$$
--
--   It replaces the scalar contraction Lemma 3 in the multiclass analysis (part 2 of Theorem 10).
--
--   Differences from the source:
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: R̂^multi real; ϕ : 𝒵 → ℝ^{k'} L-Lipschitz → radMulti valued in EReal and the inequality read in EReal (R̂^vec coerced from ℝ≥0∞); ϕ defined on ℝ^k with LipschitzOnWith L ϕ Z (L : ℝ≥0) and F valued in Z; reason: R̂^multi may be +∞ and its inner supremum may be negative; values of ϕ off 𝒵 are never used
--   - encoding: B_ϕ a bound on the norms ‖ϕ(f(X_i))‖₂ → hypothesis 0 ≤ Bφ; reason: implied by the norm bound whenever n ≥ 1 (F nonempty); without it the empty sample n = 0 makes the bound hypothesis vacuous and the claim 0 ≤ B_ϕ false for B_ϕ < 0
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 22, Lemma 4 (proof pp. 56–57, App. C.1)

import Mathlib
import Definitions.Def_HiddenCorr_ERM_Complexity

universe u

namespace HiddenCorr.ERM

/-- **Lemma 4** (vector-valued contraction), p. 22. Let `F` be a nonempty class of functions
`X → ℝ^k` with values in `Z ⊆ ℝ^k`, let `φ : Z → ℝ^{k'}` (`k' ≥ 1`) be `L`-Lipschitz, and let
`X = (X₁, …, Xₙ)` be a sample with `sup_{f ∈ F} maxᵢ ‖φ(f(Xᵢ))‖₂ ≤ B_φ` (a norm bound, `B_φ ≥ 0`). Then
`R̂^vec_X(φ ∘ F) ≤ √2 L R̂^multi_X(F) + B_φ`. -/
theorem lemma_4 {𝒳 : Type u} (k k' : ℕ) (hk' : 1 ≤ k')
    (F : Set (𝒳 → EuclideanSpace ℝ (Fin k))) (hF : F.Nonempty)
    (Z : Set (EuclideanSpace ℝ (Fin k))) (hFZ : ∀ f ∈ F, ∀ x, f x ∈ Z)
    (φ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k')) (L : NNReal)
    (hφ : LipschitzOnWith L φ Z) (n : ℕ) (X : Fin n → 𝒳) (Bφ : ℝ) (hBφ : 0 ≤ Bφ)
    (hB : ∀ f ∈ F, ∀ i, ‖φ (f (X i))‖ ≤ Bφ) :
    (radVec X ((fun f => φ ∘ f) '' F) : EReal) ≤
      ((Real.sqrt 2 * (L : ℝ) : ℝ) : EReal) * radMulti X F + (Bφ : EReal) := by sorry

end HiddenCorr.ERM
