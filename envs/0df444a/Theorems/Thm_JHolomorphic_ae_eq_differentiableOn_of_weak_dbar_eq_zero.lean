-- Prove2me | Theorems.Thm_JHolomorphic_ae_eq_differentiableOn_of_weak_dbar_eq_zero
-- name    : JHolomorphic.ae_eq_differentiableOn_of_weak_dbar_eq_zero
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T20:32:21.321575+00:00
-- url     : https://prove2.me/theorems/49f6d532-7dca-49b5-b925-a3dff0defc6a
-- title:
--   Weakly holomorphic integrable functions are holomorphic
-- statement:
--   Let $D\subset\mathbb{C}$ be the open unit disc and let $u\in L^1(D,\mathbb{C}^n)$ satisfy $\partial_su+i\,\partial_tu=0$ in the sense of distributions:
--   $$\int\big((\partial_s\varphi)\,u+(\partial_t\varphi)\,i\,u\big)=0$$
--   for every real $C^\infty$ function $\varphi$ with compact support in $D$. Then $u$ agrees almost everywhere on $D$ with a holomorphic function $v:D\to\mathbb{C}^n$.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. Integrability is `IntegrableOn u (ball 0 1)`; holomorphy is `DifferentiableOn ℂ v (ball 0 1)` and the agreement is `u =ᵐ[volume.restrict (ball 0 1)] v`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Lemma 2.19, p. 35

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Lemma 2.19 (p. 35): an integrable `u` on the open unit disc that satisfies `∂̄u = 0` in
the sense of distributions, i.e. `∫ (∂ₛφ) u + (∂ₜφ) i u = 0` for every real `C^∞` function `φ`
with compact support in the disc, agrees almost everywhere with a holomorphic function. -/
theorem ae_eq_differentiableOn_of_weak_dbar_eq_zero (n : ℕ)
    (u : ℂ → EuclideanSpace ℂ (Fin n)) (hu : IntegrableOn u (ball 0 1))
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      ∫ z, (fderiv ℝ φ z 1 • u z + fderiv ℝ φ z Complex.I • (Complex.I • u z)) = 0) :
    ∃ v : ℂ → EuclideanSpace ℂ (Fin n), DifferentiableOn ℂ v (ball 0 1) ∧
      u =ᵐ[volume.restrict (ball 0 1)] v := by
  sorry

end JHolomorphic
