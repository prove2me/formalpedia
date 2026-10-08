-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_eq_9
-- name    : HuImkellerMuller.Exponential.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:11.033208+00:00
-- url     : https://prove2.me/theorems/b9448acc-8248-4495-b96a-3602adb07d40
-- title:
--   p. 9 — dist²(z + θ_t/α, C_t) ≤ 2|z|² + 2(|θ_t|/α + k₁)² and the growth bound (9) |f(t,z)| ≤ c₀ + c₁|z|²
-- statement:
--   Assume the standing market hypotheses, let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, $\alpha>0$, and let $f(t,z)$ be the driver of the BSDE (7). Then:
--
--   1. for every constant $k_1$ satisfying (4), that is $\min\{|a|:a\in C_t(\omega)\}\le k_1$ for $\lambda\otimes P$-a.e. $(t,\omega)$, one has for $\lambda\otimes P$-a.e. $(t,\omega)$ and all $z\in\mathbb R^m$
--   $$\operatorname{dist}^2\Big(z+\frac1\alpha\theta_t,\,C_t\Big)\le 2|z|^2+2\Big(\frac1\alpha|\theta_t|+k_1\Big)^2;$$
--   2. there are constants $c_0,c_1$ such that, for $\lambda\otimes P$-a.e. $(t,\omega)$,
--   $$|f(t,z)|\le c_0+c_1|z|^2\qquad\text{for all } z\in\mathbb R^m. \tag{9}$$
--
--   The growth bound (9) is condition (H1) of Kobylanski's existence theorem for quadratic BSDEs, which yields a solution of (7).
--
--   **Formalization Note** The page writes "for all $z\in\mathbb R^n$ $P$-a.s." in (9); $z$ ranges over $\mathbb R^m$ and the qualifier is read $\lambda\otimes P$-a.e. The constants $c_0,c_1$ are uniform: they are chosen before $(t,\omega)$ and $z$. $\tilde C\ne\emptyset$ is added, as in (4).
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, (9) and the display after "By means of (4)", p. 9

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- p. 9: by (4), dist²(z + θ_t/α, C_t) ≤ 2|z|² + 2(|θ_t|/α + k₁)², and the growth bound (9)
|f(t, z)| ≤ c₀ + c₁|z|² holds. -/
theorem eq_9
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (hmkt : MarketHyp P 𝓕 T b σ)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    (α : ℝ) (hα : 0 < α) :
    (∀ k₁ : ℝ, (∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
        ∃ a ∈ Cset Ct σ q.1.toNNReal q.2, ‖a‖ ≤ k₁) →
      ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T), ∀ z : EuclideanSpace ℝ (Fin m),
        Metric.infDist (z + (1 / α) • theta b σ q.1.toNNReal q.2) (Cset Ct σ q.1.toNNReal q.2) ^ 2
          ≤ 2 * ‖z‖ ^ 2 + 2 * ((1 / α) * ‖theta b σ q.1.toNNReal q.2‖ + k₁) ^ 2) ∧
    ∃ c₀ c₁ : ℝ, ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T), ∀ z : EuclideanSpace ℝ (Fin m),
      |driver b σ Ct α q.1.toNNReal q.2 z| ≤ c₀ + c₁ * ‖z‖ ^ 2 := by sorry

end HuImkellerMuller.Exponential
