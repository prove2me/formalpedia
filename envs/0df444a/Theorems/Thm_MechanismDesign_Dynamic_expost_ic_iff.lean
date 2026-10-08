-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_expost_ic_iff
-- name    : MechanismDesign.Dynamic.expost_ic_iff
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-03T05:53:36.311254+00:00
-- url     : https://prove2.me/theorems/850cb3bd-71e3-47f9-94b9-d59cbb125d54
-- title:
--   Proposition 11.3 -- incentive compatibility with respect to the ex post type $\theta$
-- statement:
--   A direct mechanism $(q,t)$ in the sequential screening model is incentive-compatible with respect to the ex post type $\theta$ (Eq. (11.1)) if and only if:
--
--   1. for every ex ante type $\tau$, $q(\tau,\theta)$ is increasing in $\theta$;
--   2. for every ex ante type $\tau$, $u(\tau,\theta)$ is absolutely continuous in $\theta$ on $[\underline\theta,\bar\theta]$, differentiable at all but countably many points of $(\underline\theta,\bar\theta)$, and $\partial u(\tau,\theta)/\partial\theta=q(\tau,\theta)$ wherever it is differentiable;
--   3. for every $\tau$ and $\theta$,
--   $$t(\tau,\theta)=t(\tau,\underline\theta)+\bigl(\theta q(\tau,\theta)-\underline\theta q(\tau,\underline\theta)\bigr)-\int_{\underline\theta}^{\theta}q(\tau,\hat\theta)\,d\hat\theta .$$
--
--   This is the static characterization of Chapter 2 applied to each ex ante type separately.
--
--   **Formalization Note** Differentiability and the derivative formula are stated at interior points $\theta\in(\underline\theta,\bar\theta)$, where the two-sided derivative is determined by the values on the interval.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.210, Proposition 11.3

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.3**, p.210. A direct mechanism is incentive-compatible with respect to the
ex post type `θ` if and only if:
(i) for every ex ante type `τ`, `q(τ, θ)` is increasing in `θ`;
(ii) for every ex ante type `τ`, `u(τ, θ)` is absolutely continuous in `θ` on `[θ̲, θ̄]`; it is
differentiable at all but countably many points of `(θ̲, θ̄)`, and wherever it is differentiable
in `θ`, `∂u(τ, θ)/∂θ = q(τ, θ)`;
(iii) for every `τ` and `θ`:
`t(τ, θ) = t(τ, θ̲) + (θ q(τ, θ) − θ̲ q(τ, θ̲)) − ∫_{θ̲}^{θ} q(τ, θ̂) dθ̂`. -/
theorem expost_ic_iff {τlo τhi θlo θhi : ℝ} (m : DirectMechanism τlo τhi θlo θhi) :
    m.IsExPostIC ↔
      (∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (m.q τ) (Set.Icc θlo θhi)) ∧
      (∀ τ ∈ Set.Icc τlo τhi,
        AbsolutelyContinuousOnInterval (m.u τ) θlo θhi ∧
        {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ (m.u τ) θ}.Countable ∧
        ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ (m.u τ) θ → deriv (m.u τ) θ = m.q τ θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.t τ θ = m.t τ θlo + (θ * m.q τ θ - θlo * m.q τ θlo) - ∫ x in θlo..θ, m.q τ x) := by sorry

end MechanismDesign.Dynamic
