-- Prove2me | Theorems.Thm_HunterPDE_Semigroup_hille_yosida_contraction
-- name    : HunterPDE.Semigroup.hille_yosida_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:08:56.056982+00:00
-- url     : https://prove2.me/theorems/2c491149-6bef-4265-a085-709ba6f9ed7e
-- title:
--   Corollary 5.36 — Hille–Yosida theorem for contraction semigroups
-- statement:
--   Let $X$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and $A : \mathcal{D}(A) \subset X \to X$ a linear operator. Then $A$ is the generator of a strongly continuous contraction semigroup $\{T(t) : t \ge 0\}$ on $X$ if and only if
--
--   1. $\mathcal{D}(A)$ is dense in $X$ and $A$ is closed;
--   2. every real $\lambda > 0$ belongs to the resolvent set of $A$;
--   3. for every $\lambda > 0$,
--   $$\|R(\lambda, A)\| \le \frac{1}{\lambda}.$$
--
--   This is the case $M = 1$, $a = 0$ of the Hille–Yosida theorem, and the resolvent form of the Lumer–Phillips theorem.
--
--   **Formalization Note.** The operator-norm bound is stated pointwise, $\|R(\lambda, A) g\| \le \lambda^{-1}\|g\|$ for every $g \in X$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 146, Corollary 5.36

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup
import Definitions.Def_HunterPDE_Semigroup_Resolvent

namespace HunterPDE.Semigroup

/-- Corollary 5.36 of Hunter, *Notes on PDEs* (p. 146). A linear operator `A : D(A) ⊂ X → X`
in a Banach space `X` is the generator of a strongly continuous contraction semigroup on `X` if
and only if (1) `D(A)` is dense in `X` and `A` is closed; (2) every real `λ > 0` is in the
resolvent set of `A`; (3) for `λ > 0`, `‖R(λ, A)‖ ≤ 1/λ` (5.26), written pointwise as
`‖R(λ, A) g‖ ≤ (1/λ)‖g‖` for all `g ∈ X`. -/
theorem hille_yosida_contraction {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (A : X →ₗ.[𝕜] X) :
    (∃ T : ℝ → X →L[𝕜] X, IsContractionSemigroup T ∧ IsGenerator T A) ↔
      (Dense (A.domain : Set X) ∧ A.IsClosed) ∧
      (∀ lam : ℝ, 0 < lam → IsInResolventSet A (lam : 𝕜)) ∧
      (∀ lam : ℝ, 0 < lam → ∀ g : X, ‖resolvent A (lam : 𝕜) g‖ ≤ 1 / lam * ‖g‖) := by sorry

end HunterPDE.Semigroup
