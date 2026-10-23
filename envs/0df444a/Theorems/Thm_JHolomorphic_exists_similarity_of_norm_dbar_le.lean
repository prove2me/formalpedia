-- Prove2me | Theorems.Thm_JHolomorphic_exists_similarity_of_norm_dbar_le
-- name    : JHolomorphic.exists_similarity_of_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T11:46:21.462408+00:00
-- url     : https://prove2.me/theorems/9f738eb1-a120-4e9f-8676-af072aa68857
-- title:
--   Similarity principle for $\mathbb{C}^n$-valued maps with $|\bar\partial g|\le M|g|$
-- statement:
--   Let $\rho>0$, $M\in\mathbb{R}$, and let $g:\mathbb{C}\to\mathbb{C}^n$ be $C^1$ on the disc $D_\rho$ with
--   $$\big\|\partial_sg(z)+i\,\partial_tg(z)\big\|\le M\,\|g(z)\|\qquad(z\in D_\rho),$$
--   where $z=s+it$. Then there are $\varepsilon>0$, a map $\Phi$ from the closed disc $\bar D_\varepsilon$ to the complex-linear maps $\mathbb{C}^n\to\mathbb{C}^n$, continuous on $\bar D_\varepsilon$ with every $\Phi(z)$ bijective, and a holomorphic $f:D_\varepsilon\to\mathbb{C}^n$, such that
--   $$g(z)=\Phi(z)\,f(z)\qquad(z\in D_\varepsilon).$$
--
--   This is the similarity principle for maps satisfying a linear Cauchy–Riemann differential inequality: locally such a map is a continuous, pointwise invertible linear transformation of a holomorphic map. Consequences include that zeros of a nontrivial solution are isolated and have positive local multiplicity.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`; $\partial_sg(z)$, $\partial_tg(z)$ are `fderiv ℝ g z 1`, `fderiv ℝ g z Complex.I`; $\Phi$ has type `ℂ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` with `ContinuousOn Φ (closedBall 0 ε)`, and $f$ satisfies `DifferentiableOn ℂ f (ball 0 ε)`. No upper bound on $\varepsilon$ is asserted.
-- source:
--   Carleman similarity principle (Bers–Vekua); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Let `g : ℂ → ℂⁿ` be `C¹` on the disc `D_ρ` with `‖∂ₛg + i ∂ₜg‖ ≤ M ‖g‖` on `D_ρ`. Then for some
`ε > 0` there are a continuous `Φ : D̄_ε → End_ℂ(ℂⁿ)` with every `Φ(z)` bijective and a holomorphic
`f : D_ε → ℂⁿ` with `g = Φ f` on `D_ε`. -/
theorem exists_similarity_of_norm_dbar_le (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContDiffOn ℝ 1 g (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, g z = Φ z (f z) := by
  sorry

end JHolomorphic
