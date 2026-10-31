-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_theorem_2_7
-- name    : KallMayerSLP.NormalCC.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:59.729513+00:00
-- url     : https://prove2.me/theorems/e16acdb1-7508-4ef5-a05a-dfd5d6b64943
-- title:
--   Theorem 2.7 (Marti 1971): under a non-degenerate multivariate Cauchy distribution $\mathcal B(\alpha)$ is convex for $\alpha\ge\frac12$
-- statement:
--   Let the $(n+1)$-dimensional random vector $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ on a probability space have a non-degenerate multivariate Cauchy distribution (Definition 2.2), and let $\alpha\ge\frac12$. Then the set
--   $$\mathcal B(\alpha)=\{x\in\mathbb R^n\mid G(x)\ge\alpha\},\qquad G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi),$$
--   is convex.
--
--   This is the analogue of Kataoka's Theorem 2.5 for the Cauchy distribution, whose components have no expected value: the Euclidean norm of the normal case is replaced by the $\ell_1$-norm.
--
--   **Formalization Note** Every real $\alpha\ge\frac12$ is covered, including $\alpha\ge1$.
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic (no d ∈ ℝⁿ with η = d a.s.), which excludes n = 0 → n = 0 allowed (for n ≥ 1 non-degeneracy already makes η non-constant); reason: the statement remains true for n = 0 and specializes to the book's for n ≥ 1
--   - encoding: ζ = (ηᵀ, ξ)ᵀ ∈ ℝⁿ⁺¹ → Fin.snoc (η ω) (ξ ω) : Fin (n+1) → ℝ, ξ the last coordinate; reason: Lean convention; same object
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Theorem 2.7, p.116 (PDF p.126)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateCauchy
import Definitions.Def_KallMayerSLP_NormalCC_levelSet

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **Theorem 2.7 (Marti 1971)** (Kall & Mayer 2005, Chapter 2, Theorem 2.7, p.116, PDF p.126):
"Let the `(n+1)`-dimensional random vector `ζᵀ = (ηᵀ, ξ)ᵀ` have a non-degenerate multivariate
Cauchy distribution and let `α ≥ 1/2`. Then the set `B(α) = { x | G(x) ≥ α }` is convex."

Non-degenerate multivariate Cauchy is Definition 2.2 (p.115); `G(x) = ℙ(ηᵀx ≥ ξ)`.

**Formalization Note.** `(ηᵀ, ξ)ᵀ` is `Fin.snoc (η ω) (ξ ω)`; `B(α) = levelSet P η ξ α`. Every
real `α ≥ 1/2` is covered. -/
theorem theorem_2_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hζ : IsNonDegenerateMultivariateCauchy P
      (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω)))
    (α : ℝ) (hα : 1 / 2 ≤ α) :
    Convex ℝ (levelSet P η ξ α) := by sorry

end KallMayerSLP.NormalCC
