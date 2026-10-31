-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_theorem_2_5
-- name    : KallMayerSLP.NormalCC.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:52.383896+00:00
-- url     : https://prove2.me/theorems/efe254f4-2231-42b0-b7ac-bb920d666d01
-- title:
--   Theorem 2.5 (Kataoka; van de Panne–Popp): under a multivariate normal distribution $\mathcal B(\alpha)$ is convex for $\alpha\ge\frac12$
-- statement:
--   Let the $(n+1)$-dimensional random vector $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ have a multivariate normal distribution in the sense of Definition 2.1 (degenerate distributions allowed), and let $\alpha\ge\frac12$. Then the set
--   $$\mathcal B(\alpha)=\{x\in\mathbb R^n\mid G(x)\ge\alpha\},\qquad G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi),$$
--   is convex.
--
--   This is the classical convexity result for separate (individual) chance constraints with a random technology row: for reliability levels at least one half, the constraint $\mathbb P(\eta^{\mathsf T}x\ge\xi)\ge\alpha$ can be imposed in a convex program. Theorem 2.6 shows that the level $\frac12$ cannot be lowered.
--
--   **Formalization Note** Every real $\alpha\ge\frac12$ is covered, including $\alpha\ge1$ (where $\mathcal B(\alpha)$ is $\{x\mid G(x)=1\}$ or empty).
--
--   Differences from the source:
--   - generalization: standing assumption of §2.3.2 (p.103): η is stochastic, i.e. there is no d ∈ ℝⁿ with η = d a.s. (this also excludes n = 0) → not assumed; η may be a.s. constant and n = 0 is allowed; reason: the conclusion holds for every (η, ξ) of the stated form, and the book's case is the special case where η is not a.s. constant
--   - encoding: ζ = (ηᵀ, ξ)ᵀ ∈ ℝⁿ⁺¹ → Fin.snoc (η ω) (ξ ω) : Fin (n+1) → ℝ, ξ the last coordinate; reason: Lean convention; same object
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Theorem 2.5, p.107 (PDF p.117)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsMultivariateNormal
import Definitions.Def_KallMayerSLP_NormalCC_levelSet

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **Theorem 2.5 (Kataoka 1963; van de Panne and Popp 1963)** (Kall & Mayer 2005, Chapter 2,
Theorem 2.5, p.107, PDF p.117): "Let the `(n + 1)`-dimensional random vector `ζᵀ = (ηᵀ, ξ)ᵀ`
have a multivariate normal distribution and let `α ≥ 1/2`. Then the set
`B(α) = { x | G(x) ≥ α }` is convex."

Here `G(x) = ℙ(ηᵀx ≥ ξ)` ((2.31)), and "multivariate normal" is Definition 2.1 (degenerate
distributions allowed).

**Formalization Note.** `(ηᵀ, ξ)ᵀ ∈ ℝ^{n+1}` is `Fin.snoc (η ω) (ξ ω)` (`ξ` is the last
coordinate). `B(α) = levelSet P η ξ α`. Every real `α ≥ 1/2` is covered, including `α ≥ 1`.
The standing assumption of §2.3.2 that `η` is not almost surely constant is not assumed. -/
theorem theorem_2_5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hζ : IsMultivariateNormal P (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω)))
    (α : ℝ) (hα : 1 / 2 ≤ α) :
    Convex ℝ (levelSet P η ξ α) := by sorry

end KallMayerSLP.NormalCC
