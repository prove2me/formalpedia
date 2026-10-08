-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_optimal_sequential_screening
-- name    : MechanismDesign.Dynamic.optimal_sequential_screening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:11:20.65598+00:00
-- url     : https://prove2.me/theorems/1d94358a-70b7-4500-889e-7d59e6611c91
-- title:
--   Proposition 11.8 -- optimal sequential screening by a menu of option contracts (Courty–Li)
-- statement:
--   Consider the sequential screening model and suppose Assumption 11.1 holds: the virtual valuation $\psi(\tau,\theta)=\theta+\frac{1-G(\tau)}{g(\tau)}\frac{\partial F(\theta\mid\tau)/\partial\tau}{f(\theta\mid\tau)}$ is increasing in $\tau$ and $\theta$. Let $p(\tau)=\min\{\hat\theta\in[\underline\theta,\bar\theta]\mid\psi(\tau,\hat\theta)\ge0\}$ and define
--
--   $$q^*(\tau,\theta)=\begin{cases}1&\theta\ge p(\tau),\\0&\text{otherwise,}\end{cases}\qquad t^*(\tau,\theta)=\begin{cases}t_0(\tau)+p(\tau)&\theta\ge p(\tau),\\t_0(\tau)&\text{otherwise,}\end{cases}\qquad(11.10),(11.11)$$
--
--   where $t_0(\tau)$ is given by Proposition 11.5 for the allocation rule $q^*$ and the lowest-type payment
--
--   $$t(\underline\tau,\underline\theta)=\int_{p(\underline\tau)}^{\bar\theta}\hat\theta f(\hat\theta\mid\underline\tau)\,d\hat\theta-p(\underline\tau)\bigl[1-F(p(\underline\tau)\mid\underline\tau)\bigr]+\underline\theta q^*(\underline\tau,\underline\theta).\qquad(11.12)$$
--
--   Then:
--
--   1. a (measurable) direct mechanism equal to $(q^*,t^*)$ on $[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]$ exists, and every such mechanism is incentive-compatible, individually rational and optimal;
--   2. an admissible, incentive-compatible and individually rational direct mechanism $(q,t)$ is optimal if and only if $q=q^*$ almost everywhere on $\{\psi\ne0\}$ and $U(\underline\tau)=0$;
--   3. if $\{\psi=0\}$ has probability zero, an admissible, incentive-compatible and individually rational direct mechanism $(q,t)$ is optimal if and only if $q=q^*$ and $t=t^*$ almost everywhere.
--
--   The optimal mechanism is a menu of option contracts: ex ante type $\tau$ pays the fee $t_0(\tau)$ for the option to buy the good later at the exercise price $p(\tau)$, and exercises it exactly when $\theta\ge p(\tau)$. This is the capstone of §11.2.1.
--
--   **Formalization Note** "Almost everywhere" refers to the joint distribution of $(\tau,\theta)$, with density $g(\tau)f(\theta\mid\tau)$. The page states "optimal if and only if (11.10)–(11.12)" for all $(\tau,\theta)$. The "if" direction is item 1. The "only if" direction is false pointwise (the value of $q$ on a null set, e.g. at $\theta=p(\tau)$, does not affect revenue) and false on any set of positive probability where $\psi=0$ (there $q$ does not affect revenue either); items 2 and 3 state the necessity that holds. $p(\tau)$ is the infimum of the set, which equals the minimum when the minimum exists. Optimality is among admissible (measurable) mechanisms, randomized $q\in[0,1]$ included.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.217–218, Proposition 11.8, Eq. (11.10)–(11.12)

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

open MeasureTheory

namespace MechanismDesign.Dynamic

/-- **Proposition 11.8** (Courty–Li), pp.217–218. Suppose Assumption 11.1 holds. Let
`q*(τ, θ) = 1` if `θ ≥ p(τ)` and `0` otherwise (11.10), and `t*(τ, θ) = t₀(τ) + p(τ)` if
`θ ≥ p(τ)` and `t₀(τ)` otherwise (11.11), where `t₀` is given by Proposition 11.5 with
`t(τ̲, θ̲) = ∫_{p(τ̲)}^{θ̄} θ̂ f(θ̂|τ̲) dθ̂ − p(τ̲)[1 − F(p(τ̲)|τ̲)] + θ̲ q*(τ̲, θ̲)` (11.12).

1. A (measurable) direct mechanism equal to `(q*, t*)` on `[τ̲, τ̄] × [θ̲, θ̄]` exists.
2. Every admissible direct mechanism equal to `(q*, t*)` on `[τ̲, τ̄] × [θ̲, θ̄]` is
   incentive-compatible, individually rational and optimal.
3. An admissible, incentive-compatible and individually rational direct mechanism `(q, t)` is
   optimal if and only if `q = q*` almost everywhere on `{ψ ≠ 0}` and `U(τ̲) = 0`.
4. If `{ψ = 0}` is a null set, an admissible, incentive-compatible and individually rational
   direct mechanism `(q, t)` is optimal if and only if `q = q*` and `t = t*` almost everywhere.

"Almost everywhere" is with respect to the joint distribution of `(τ, θ)`. The page states the
characterization "if and only if (11.10)–(11.12)" pointwise; its necessity half holds only almost
everywhere and only off `{ψ = 0}`, which is what items 3–4 state. -/
theorem optimal_sequential_screening {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (hA : E.Assumption11_1) :
    (∃ m : DirectMechanism τlo τhi θlo θhi, m.Admissible ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ) ∧
    (∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible →
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ) →
      m.IsIC E ∧ m.IsIR E ∧ m.IsOptimal E) ∧
    (∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible → m.IsIC E → m.IsIR E →
      (m.IsOptimal E ↔
        (∀ᵐ p ∂E.jointLaw, E.ψ p.1 p.2 ≠ 0 → m.q p.1 p.2 = E.optQ p.1 p.2) ∧
          m.U E τlo = 0)) ∧
    (E.jointLaw {p | E.ψ p.1 p.2 = 0} = 0 →
      ∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible → m.IsIC E → m.IsIR E →
        (m.IsOptimal E ↔
          (∀ᵐ p ∂E.jointLaw, m.q p.1 p.2 = E.optQ p.1 p.2) ∧
            ∀ᵐ p ∂E.jointLaw, m.t p.1 p.2 = E.optT p.1 p.2)) := by sorry

end MechanismDesign.Dynamic
