-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_lemma_3_2
-- name    : GPhNGIDiffusion.OccupationCLT.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:18.835967+00:00
-- url     : https://prove2.me/theorems/57b23805-edf1-4878-a30c-81151ae742f6
-- title:
--   Lemma 3.2, p. 12 — the Stein solution f = −∫₀^∞ P_t[h − μ(h)]dt is well defined, solves (3.1), and has the resolvent representation
-- statement:
--   Let $(X_t)$ be the limiting diffusion (1.1) with semigroup $(P_t)$ and invariant probability measure $\mu$, and let $h:\mathbb R^d\to\mathbb R$ be bounded and measurable. Let $f$ be the function (3.2).
--
--   1. For every $x$, the function $t\mapsto P_th(x)-\mu(h)$ is integrable on $(0,\infty)$, so
--   $$
--   f(x)=-\int_0^\infty P_t[h(x)-\mu(h)]\,dt
--   $$
--   is well defined.
--   2. $f$ solves the Stein equation $\mathcal Af=h-\mu(h)$ (3.1) in integrated form: for all $x$ and $t\ge0$, $f(X^x_t)$ is integrable and
--   $$
--   P_tf(x)-f(x)=\int_0^t\big(P_sh(x)-\mu(h)\big)\,ds .
--   $$
--   3. For every $\lambda>0$ and $x$, the integrand below is integrable and
--   $$
--   f(x)=\int_0^\infty e^{-\lambda t}P_t[\lambda f(x)-h(x)+\mu(h)]\,dt .
--   $$
--
--   The resolvent form (3) is what allows the gradient of $f$ to be estimated through derivatives of $P_t$ applied to $\lambda f-h+\mu(h)$.
--
--   **Formalization Note** For bounded measurable $h$ the function $f$ need not be $C^2$, so "solution to (3.1)" is rendered in the integrated (Dynkin) form of item 2, the sense in which the paper's proof (via Fang et al. [24, Prop. 6.1]) uses it. Item 3 is part (ii).
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 12, Lemma 3.2 (proof pp. 31–32)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Occupation
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Lemma 3.2, p. 12. For bounded measurable `h`:
(i) `t ↦ P_t h(x) − μ(h)` is integrable on `(0, ∞)`, so `f(x) = −∫₀^∞ (P_t h(x) − μ(h)) dt`
(3.2) is well defined, and `f` solves (3.1) in integrated form:
`f(X^x_t)` is integrable and `P_t f(x) − f(x) = ∫₀ᵗ (P_s h(x) − μ(h)) ds` for all `t ≥ 0`;
(ii) for every `λ > 0`, `f(x) = ∫₀^∞ e^{−λt} P_t[λf − h + μ(h)](x) dt` (integrand integrable). -/
theorem lemma_3_2 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (μ : Measure (E d)) [IsProbabilityMeasure μ] (hμ : IsInvariant P X μ)
    (h : E d → ℝ) (hh : Measurable h) (hb : ∃ K : ℝ, ∀ y, |h y| ≤ K) :
    (∀ x : E d,
      IntegrableOn (fun t : ℝ => semigroup P X t.toNNReal h x - ∫ y, h y ∂μ) (Set.Ioi 0)) ∧
    (∀ (x : E d) (t : ℝ≥0),
      Integrable (fun ω => steinSol P X μ h (X x t ω)) P ∧
      semigroup P X t (steinSol P X μ h) x - steinSol P X μ h x
        = ∫ s in (0 : ℝ)..(t : ℝ), (semigroup P X s.toNNReal h x - ∫ y, h y ∂μ)) ∧
    (∀ l : ℝ, 0 < l → ∀ x : E d,
      IntegrableOn (fun t : ℝ => Real.exp (-(l * t)) *
          semigroup P X t.toNNReal (fun y => l * steinSol P X μ h y - h y + ∫ z, h z ∂μ) x)
        (Set.Ioi 0) ∧
      steinSol P X μ h x
        = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(l * t)) *
            semigroup P X t.toNNReal (fun y => l * steinSol P X μ h y - h y + ∫ z, h z ∂μ) x) := by sorry

end GPhNGIDiffusion.OccupationCLT
