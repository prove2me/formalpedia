-- Prove2me | Theorems.Thm_KallMayerSLP_NormalCC_theorem_2_6
-- name    : KallMayerSLP.NormalCC.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:55.714387+00:00
-- url     : https://prove2.me/theorems/0534cea8-affa-492e-aa57-eb4c6e1eff79
-- title:
--   Theorem 2.6 (Kall 1976): for $\alpha<\frac12$, $\mathcal B(\alpha)=\mathbb R^n$ or $\mathcal B(\alpha)$ is non-convex
-- statement:
--   Let $n>1$ and let the $(n+1)$-dimensional random vector $\zeta=(\eta^{\mathsf T},\xi)^{\mathsf T}$ on a probability space have a non-degenerate multivariate normal distribution (covariance matrix positive definite). Let $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$ and $\mathcal B(\alpha)=\{x\in\mathbb R^n\mid G(x)\ge\alpha\}$. If $\alpha<\frac12$, then
--   $$\mathcal B(\alpha)=\mathbb R^n\quad\text{or}\quad \mathcal B(\alpha)\text{ is not convex}.$$
--
--   Together with Theorem 2.5 this shows that the threshold $\alpha=\frac12$ is sharp for convexity of separate normal chance constraints.
--
--   **Formalization Note** Every real $\alpha<\frac12$ is covered, including $\alpha\le0$ (where $\mathcal B(\alpha)=\mathbb R^n$).
--
--   Differences from the source:
--   - encoding: ζ = (ηᵀ, ξ)ᵀ ∈ ℝⁿ⁺¹ → Fin.snoc (η ω) (ξ ω) : Fin (n+1) → ℝ, ξ the last coordinate; reason: Lean convention; same object
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Theorem 2.6, p.107 (PDF p.117)

import Mathlib
import Definitions.Def_KallMayerSLP_NormalCC_IsNonDegenerateMultivariateNormal
import Definitions.Def_KallMayerSLP_NormalCC_levelSet

open MeasureTheory ProbabilityTheory Matrix

namespace KallMayerSLP.NormalCC

/-- **Theorem 2.6 (Kall 1976)** (Kall & Mayer 2005, Chapter 2, Theorem 2.6, p.107, PDF p.117):
"Let `n > 1` and assume that the `(n + 1)`-dimensional random vector `ζᵀ = (ηᵀ, ξ)ᵀ` has a
non-degenerate multivariate normal distribution. If `α < 1/2` then either `B(α) = ℝⁿ` holds or
otherwise `B(α)` is a non-convex set."

**Formalization Note.** Non-degenerate is `IsNonDegenerateMultivariateNormal` (p.104: covariance
matrix positive definite). `(ηᵀ, ξ)ᵀ` is `Fin.snoc (η ω) (ξ ω)`; `B(α) = levelSet P η ξ α`. Every
real `α < 1/2` is covered, including `α ≤ 0`. -/
theorem theorem_2_6 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 1 < n) (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hζ : IsNonDegenerateMultivariateNormal P
      (fun ω => Fin.snoc (α := fun _ => ℝ) (η ω) (ξ ω)))
    (α : ℝ) (hα : α < 1 / 2) :
    levelSet P η ξ α = Set.univ ∨ ¬ Convex ℝ (levelSet P η ξ α) := by sorry

end KallMayerSLP.NormalCC
