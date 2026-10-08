-- Prove2me | Theorems.Thm_MussaRosen_Mono_mu_eq_integral_MR_sub_MC
-- name    : MussaRosen.Mono.mu_eq_integral_MR_sub_MC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:17.232259+00:00
-- url     : https://prove2.me/theorems/1e4300b8-05df-44c1-84c2-4733c882d009
-- title:
--   (10) = (12), p. 309 — μ(t) = ∫_t^θ̄ [MR(θ) − C′(q(θ))] f(θ) dθ
-- statement:
--   Let $f$ be a positive, differentiable density on $[\underline\theta,\bar\theta]$ with distribution function $F$, let $C$ be a cost function whose derivative $C'$ is differentiable, and let $q$ be an admissible assignment (nondecreasing, nonnegative, piecewise differentiable on $[\underline\theta,\bar\theta]$). For $t\in[\underline\theta,\bar\theta]$ let
--   $$\mu(t)=\int_{t}^{\bar\theta}\Bigl[\theta-\int_t^{\theta}ds-C'(q(\theta))\Bigr]f(\theta)\,d\theta$$
--   be the marginal profit (10) of raising quality by one unit for all types $\theta\ge t$. Then
--   $$\mu(t)=\int_t^{\bar\theta}\bigl[MR(\theta)-MC(\theta)\bigr]f(\theta)\,d\theta,$$
--   where $MR(\theta)=\theta-(1-F(\theta))/f(\theta)$ and $MC(\theta)=C'(q(\theta))$. This is equation (12).
--
--   The identity expresses the effect of a uniform quality increase for all types above $t$ as the accumulated difference between marginal revenue and marginal cost, which is the form used in every later step of the argument.
--
--   **Formalization Note** The statement is an identity and does not use optimality; the paper's hypotheses $C(0)=0$, $C'>0$ and $C''>0$ are not needed and are dropped, which makes the statement stronger.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 309, §4, equations (10), (11), (12)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_eq_integral_MR_sub_MC {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ∀ t ∈ Set.Icc θlo θhi,
      mu D C q t = ∫ θ in t..θhi, (virtualValuation D θ - deriv C (q θ)) * D.f θ := by sorry

end MussaRosen.Mono
