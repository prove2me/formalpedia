-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_transfer_formula
-- name    : MechanismDesign.Dynamic.transfer_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:13:11.599776+00:00
-- url     : https://prove2.me/theorems/1b284a88-f3ca-434c-bf09-7a5027a20e82
-- title:
--   Proposition 11.5 -- the transfer schedule is pinned down up to $t(\underline\tau,\underline\theta)$
-- statement:
--   If an admissible direct mechanism in the sequential screening model is incentive-compatible, then for all $(\tau,\theta)\in[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]$
--   $$t(\tau,\theta)=t_0(\tau)+\theta q(\tau,\theta)-\int_{\underline\theta}^{\theta}q(\tau,\hat\theta)\,d\hat\theta,$$
--   where
--   $$t_0(\tau)=t(\underline\tau,\underline\theta)-\underline\theta q(\underline\tau,\underline\theta)+\int_{\underline\tau}^{\tau}\!\int_{\underline\theta}^{\bar\theta}q(\hat\tau,\hat\theta)\frac{\partial F(\hat\theta\mid\hat\tau)}{\partial\tau}\,d\hat\theta\,d\hat\tau+\int_{\underline\theta}^{\bar\theta}\!\int_{\underline\theta}^{\hat\theta}\bigl[q(\tau,x)f(\hat\theta\mid\tau)-q(\underline\tau,x)f(\hat\theta\mid\underline\tau)\bigr]\,dx\,d\hat\theta .$$
--
--   Given the allocation rule, incentive compatibility thus determines the whole transfer schedule except for the single number $t(\underline\tau,\underline\theta)$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.214, Proposition 11.5

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

namespace MechanismDesign.Dynamic

/-- **Proposition 11.5**, p.214. If an (admissible) direct mechanism is incentive-compatible, then
for all `(τ, θ) ∈ [τ̲, τ̄] × [θ̲, θ̄]`
`t(τ, θ) = t₀(τ) + θ q(τ, θ) − ∫_{θ̲}^{θ} q(τ, θ̂) dθ̂`, where
`t₀(τ) = t(τ̲, θ̲) − θ̲ q(τ̲, θ̲) + ∫_{τ̲}^{τ} ∫_{θ̲}^{θ̄} q(τ̂, θ̂) ∂F(θ̂|τ̂)/∂τ dθ̂ dτ̂
  + ∫_{θ̲}^{θ̄} ∫_{θ̲}^{θ̂} [q(τ, x) f(θ̂|τ) − q(τ̲, x) f(θ̂|τ̲)] dx dθ̂` (`SeqEnv.t0`). -/
theorem transfer_formula {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
      m.t τ θ = E.t0 m.q (m.t τlo θlo) τ + θ * m.q τ θ - ∫ x in θlo..θ, m.q τ x := by sorry

end MechanismDesign.Dynamic
