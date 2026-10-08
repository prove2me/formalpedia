-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_dynamic_revelation_principle
-- name    : MechanismDesign.Dynamic.dynamic_revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:53:12.418031+00:00
-- url     : https://prove2.me/theorems/97bf2bd1-2fe2-40cd-b14d-e34c358dec1b
-- title:
--   Proposition 11.1 -- Dynamic Revelation Principle
-- statement:
--   Consider the sequential screening model, and a general dynamic mechanism $\Gamma$ in which the buyer chooses $a_1$ before learning her valuation $\theta$ and $a_2$ after, each pair $(a_1,a_2)$ resulting in a purchase probability in $[0,1]$ and an expected payment. Let $\sigma=(\sigma_1,\sigma_2)$ be an optimal buyer strategy in $\Gamma$.
--
--   Then there are a direct mechanism $\Gamma'=(q,t)$ and an optimal buyer strategy $\sigma'=(\sigma_1',\sigma_2')$ in $\Gamma'$ such that
--
--   1. $\sigma_1'(\tau)=\tau$ for every $\tau\in[\underline\tau,\bar\tau]$, and $\sigma_2'(\tau,\theta,\tau)=\theta$ for every $\theta\in[\underline\theta,\bar\theta]$, $\tau\in[\underline\tau,\bar\tau]$: truth about $\tau$, and after a truthful report of $\tau$, truth about $\theta$;
--   2. for every $(\tau,\theta)$, $q(\tau,\theta)$ and $t(\tau,\theta)$ are the probability of purchase and the expected payment that result under $\Gamma$ when the buyer plays $\sigma$:
--   $$q(\tau,\theta)=\operatorname{prob}\bigl(\sigma_1(\tau),\sigma_2(\tau,\theta,\sigma_1(\tau))\bigr),\qquad t(\tau,\theta)=\operatorname{pay}\bigl(\sigma_1(\tau),\sigma_2(\tau,\theta,\sigma_1(\tau))\bigr).$$
--
--   The result justifies the restriction to direct mechanisms in §11.2. It says nothing about reports after a lie about $\tau$; that is why Definition 11.2(ii) quantifies over all reporting functions.
--
--   **Formalization Note** Optimality of a strategy is sequential: the second-stage choice is a best reply after every first-stage choice, and the first-stage choice maximizes expected utility given the second-stage behaviour. The general mechanism is in reduced form (the book does not formalize general mechanisms); a direct mechanism is the case $A_1=[\underline\tau,\bar\tau]$, $A_2=[\underline\theta,\bar\theta]$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.207, Proposition 11.1

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.1 (Dynamic Revelation Principle)**, p.207. For every (reduced-form) dynamic
mechanism `Γ` and every optimal buyer strategy `σ = (σ₁, σ₂)` in `Γ`, there is a direct
mechanism `Γ′ = (q, t)` and an optimal buyer strategy `σ′ = (σ′₁, σ′₂)` in `Γ′` such that
(i) `σ′₁(τ) = τ` for every `τ ∈ [τ̲, τ̄]` and `σ′₂(τ, θ, τ) = θ` for every `θ ∈ [θ̲, θ̄]`,
`τ ∈ [τ̲, τ̄]`; and (ii) for every `(τ, θ) ∈ [τ̲, τ̄] × [θ̲, θ̄]`, `q(τ, θ)` and `t(τ, θ)` equal
the probability of purchase and the expected payment that result under `Γ` when the buyer
plays `σ`. -/
theorem dynamic_revelation_principle {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (Γ : DynMechanism) (hΓ : Γ.Valid) (σ₁ : ℝ → Γ.A₁) (σ₂ : ℝ → ℝ → Γ.A₁ → Γ.A₂)
    (hσ : Γ.IsOptimalStrategy E σ₁ σ₂) :
    ∃ (m : DirectMechanism τlo τhi θlo θhi) (σ₁' : ℝ → Set.Icc τlo τhi)
      (σ₂' : ℝ → ℝ → Set.Icc τlo τhi → Set.Icc θlo θhi),
      m.toDyn.IsOptimalStrategy E σ₁' σ₂' ∧
      (∀ τ ∈ Set.Icc τlo τhi, (σ₁' τ : ℝ) = τ) ∧
      (∀ τ (hτ : τ ∈ Set.Icc τlo τhi), ∀ θ ∈ Set.Icc θlo θhi, (σ₂' τ θ ⟨τ, hτ⟩ : ℝ) = θ) ∧
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = Γ.prob (σ₁ τ) (σ₂ τ θ (σ₁ τ)) ∧ m.t τ θ = Γ.pay (σ₁ τ) (σ₂ τ θ (σ₁ τ))) := by sorry

end MechanismDesign.Dynamic
