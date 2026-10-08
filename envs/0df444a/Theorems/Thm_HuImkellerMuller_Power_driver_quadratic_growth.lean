-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_driver_quadratic_growth
-- name    : HuImkellerMuller.Power.driver_quadratic_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:51.168106+00:00
-- url     : https://prove2.me/theorems/26ace6ef-cb9a-4ada-ad50-d6d02a826590
-- title:
--   Proof of Theorem 14, p. 18 — the driver of (15) is predictable and satisfies (H1): |f(t, z)| ≤ c₀ + c₁|z|²
-- statement:
--   Assume the market hypotheses of §1, let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, and let $\gamma\in(0,1)$. Then:
--
--   1. for every $z\in\mathbb R^m$, the process $(f(t,z))_{t\in[0,T]}$ is $\mathbb F$-predictable;
--   2. there are constants $c_0,c_1$ such that, for $\lambda\otimes P$-almost every $(t,\omega)\in[0,T]\times\Omega$,
--   $$
--   |f(t,z)|\le c_0+c_1|z|^2\qquad\text{for all }z\in\mathbb R^m,
--   $$
--   where $f$ is the driver of the BSDE (15).
--
--   This is condition (H1) of Kobylanski's existence theorem for quadratic BSDEs; the paper derives it from (4) and the boundedness of $\theta$.
--
--   **Formalization Note** $\tilde C\neq\emptyset$ is added: (4), the bound $\min\{|a|:a\in C_t(\omega)\}\le k_1$ used here, needs a point of $\tilde C$. The constants come before the almost-everywhere quantifier and do not depend on $(t,\omega)$ or $z$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 14, p. 18, first paragraph; (4), p. 6; (H1) as (9), p. 9

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Proof of Theorem 14, p. 18: for every `z ∈ ℝᵐ` the driver `(f(t, z))_t` of (15) is a
predictable process, and it satisfies condition (H1) of Kobylanski's Theorem 2.3: there are
constants `c₀, c₁` with `|f(t, z)| ≤ c₀ + c₁ |z|²` for every `z ∈ ℝᵐ`, for `λ ⊗ P`-a.e. `(t, ω)`. -/
theorem driver_quadratic_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} {T : ℝ≥0} (hT : 0 < T) {𝓕 : Filtration ℝ≥0 mΩ}
    {b : ℝ≥0 → Ω → (Fin d → ℝ)} {σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ}
    (hmkt : MarketHyp P 𝓕 T b σ)
    {Ct : Set (Fin d → ℝ)} (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ z : EuclideanSpace ℝ (Fin m), HuImkellerMuller.Exponential.IsPredictable 𝓕 (fun t ω => driver b σ Ct γ t ω z)) ∧
    ∃ c₀ c₁ : ℝ, ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
      ∀ z : EuclideanSpace ℝ (Fin m),
        |driver b σ Ct γ q.1.toNNReal q.2 z| ≤ c₀ + c₁ * ‖z‖ ^ 2 := by sorry

end HuImkellerMuller.Power
