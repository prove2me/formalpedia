-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_exante_envelope
-- name    : MechanismDesign.Dynamic.exante_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:54:20.573367+00:00
-- url     : https://prove2.me/theorems/d307ca75-44b1-4cd2-ac8c-afd111beb6b4
-- title:
--   Proposition 11.4 -- envelope formula in the ex ante type $\tau$
-- statement:
--   If an admissible direct mechanism in the sequential screening model is incentive-compatible, then:
--
--   1. $U$ is differentiable at all but countably many points of $(\underline\tau,\bar\tau)$, and at any point $\tau$ of differentiability
--   $$U'(\tau)=\frac{\partial\hat U(\tau\mid\tau)}{\partial\tau}=-\int_{\underline\theta}^{\bar\theta}q(\tau,\hat\theta)\frac{\partial F(\hat\theta\mid\tau)}{\partial\tau}\,d\hat\theta,$$
--   where $\partial\hat U(\tau\mid\tau)/\partial\tau$ is the derivative of $s\mapsto\hat U(\tau\mid s)$ at $s=\tau$;
--   2. for every ex ante type $\tau$,
--   $$\int_{\underline\theta}^{\bar\theta}t(\tau,\hat\theta)f(\hat\theta\mid\tau)\,d\hat\theta=\int_{\underline\theta}^{\bar\theta}\hat\theta q(\tau,\hat\theta)f(\hat\theta\mid\tau)\,d\hat\theta+\int_{\underline\theta}^{\bar\theta}\bigl\{t(\underline\tau,\hat\theta)-\hat\theta q(\underline\tau,\hat\theta)\bigr\}f(\hat\theta\mid\underline\tau)\,d\hat\theta+\int_{\underline\tau}^{\tau}\!\int_{\underline\theta}^{\bar\theta}q(\hat\tau,\hat\theta)\frac{\partial F(\hat\theta\mid\hat\tau)}{\partial\tau}\,d\hat\theta\,d\hat\tau .$$
--
--   Part 2 is the dynamic revenue equivalence: the allocation rule and the lowest type's payments pin down each ex ante type's expected payment.
--
--   **Formalization Note** Differentiability is at interior points of $(\underline\tau,\bar\tau)$; the derivatives are stated with `HasDerivAt`, so the formula asserts that both derivatives exist.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.212–213, Proposition 11.4

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.4**, pp.212–213. If an (admissible) direct mechanism is incentive-compatible,
then:
(i) `U` is differentiable at all but countably many points of `(τ̲, τ̄)`, and at any point `τ`
of differentiability
`U′(τ) = ∂Û(τ|τ)/∂τ = −∫_{θ̲}^{θ̄} q(τ, θ̂) ∂F(θ̂|τ)/∂τ dθ̂`
(here `∂Û(τ|τ)/∂τ` is the derivative of `s ↦ Û(τ|s)` at `s = τ`);
(ii) for every ex ante type `τ`,
`∫ t(τ, θ̂) f(θ̂|τ) dθ̂ = ∫ θ̂ q(τ, θ̂) f(θ̂|τ) dθ̂ + ∫ {t(τ̲, θ̂) − θ̂ q(τ̲, θ̂)} f(θ̂|τ̲) dθ̂
  + ∫_{τ̲}^{τ} ∫_{θ̲}^{θ̄} q(τ̂, θ̂) ∂F(θ̂|τ̂)/∂τ dθ̂ dτ̂`, all `θ̂`-integrals over `[θ̲, θ̄]`. -/
theorem exante_envelope {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    ({τ ∈ Set.Ioo τlo τhi | ¬ DifferentiableAt ℝ (m.U E) τ}.Countable ∧
      ∀ τ ∈ Set.Ioo τlo τhi, DifferentiableAt ℝ (m.U E) τ →
        HasDerivAt (m.U E) (-∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ) τ ∧
        HasDerivAt (fun s => m.Uhat E τ s) (-∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ) τ) ∧
    ∀ τ ∈ Set.Icc τlo τhi,
      ∫ θ in θlo..θhi, m.t τ θ * E.f θ τ =
        (∫ θ in θlo..θhi, θ * m.q τ θ * E.f θ τ) +
        (∫ θ in θlo..θhi, (m.t τlo θ - θ * m.q τlo θ) * E.f θ τlo) +
        ∫ τ' in τlo..τ, ∫ θ in θlo..θhi, m.q τ' θ * E.dFdτ θ τ' := by sorry

end MechanismDesign.Dynamic
