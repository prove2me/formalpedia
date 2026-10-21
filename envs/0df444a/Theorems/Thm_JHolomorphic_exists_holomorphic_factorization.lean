-- Prove2me | Theorems.Thm_JHolomorphic_exists_holomorphic_factorization
-- name    : JHolomorphic.exists_holomorphic_factorization
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T20:32:58.260175+00:00
-- url     : https://prove2.me/theorems/2db01665-32b8-444c-8b5d-ba7bf364dc7a
-- title:
--   Solutions of real-linear Cauchy–Riemann equations factor locally through holomorphic maps
-- statement:
--   Let $E$ be a real vector space of dimension $2n$, let $D\subset\mathbb{C}$ be the open unit disc, and let $\bar J,A:D\to\operatorname{End}_{\mathbb{R}}(E)$ be $C^\infty$ with $\bar J(z)^2=-\mathrm{Id}$. Let $h:D\to E$ be $C^\infty$ with
--   $$\partial_sh+\bar J(z)\,\partial_th+A(z)\,h=0\quad\text{on }D.$$
--   Then there are $\varepsilon>0$, a continuous map $\Phi$ from the closed disc $\bar D_\varepsilon$ to the real-linear maps $\mathbb{C}^n\to E$, each $\Phi(z)$ bijective with $\Phi(z)(iw)=\bar J(z)\,\Phi(z)w$, and a holomorphic $f:D_\varepsilon\to\mathbb{C}^n$, such that
--   $$h(z)=\Phi(z)\,f(z)\quad\text{for }z\in D_\varepsilon.$$
--
--   **Formalization Note** Wendl's Theorem 2.26 is the case $E=\mathbb{C}^n$, $\bar J\equiv i$, and assumes in addition $h(0)=0$. $E$ is a normed space with `Module.finrank ℝ E = 2 * n`, $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, $\Phi$ has type `ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E` with `ContinuousOn Φ (closedBall 0 ε)`, and $f$ satisfies `DifferentiableOn ℂ f (ball 0 ε)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.26, p. 39, generalized to a complex structure that varies with the point

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Theorem 2.26 (p. 39), generalized to a complex structure that varies with the
point: let `E` have real dimension `2n`, let `J̄ : D → End_ℝ(E)` be smooth on the open
unit disc `D` with `J̄(z)² = -1`, let `A : D → End_ℝ(E)` be smooth, and let `h : D → E` be smooth
with `∂ₛh + J̄(z) ∂ₜh + A(z) h = 0`. For some `ε > 0` there are a continuous
`Φ : D̄_ε → Hom_ℝ(ℂⁿ, E)` with every `Φ(z)` bijective and `Φ(z) ∘ i = J̄(z) ∘ Φ(z)`, and a
holomorphic `f : D_ε → ℂⁿ` with `h = Φ f` on `D_ε`. (Wendl's Theorem 2.26 is the case
`E = ℂⁿ`, `J̄ ≡ i`; he also assumes `h(0) = 0`.) -/
theorem exists_holomorphic_factorization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar A : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (hA : ContDiffOn ℝ ∞ A (ball 0 1)) (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I) + A z (h z) = 0) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z) ∧
          ∀ w, Φ z (Complex.I • w) = Jbar z (Φ z w)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, h z = Φ z (f z) := by
  sorry

end JHolomorphic
