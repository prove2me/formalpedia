-- Prove2me | Theorems.Thm_MechanismDesign_Screening_revelation_principle
-- name    : MechanismDesign.Screening.revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:43:37.366277+00:00
-- url     : https://prove2.me/theorems/90a352a0-3050-4ea5-8def-df4779911719
-- title:
--   Proposition 2.1 -- Revelation Principle for screening
-- statement:
--   Let the buyer's type lie in $[\underline\theta,\bar\theta]$ with $0\le\underline\theta<\bar\theta$. Consider any selling mechanism $\Gamma$, described by the buyer's set of strategies $S$ and, for each $s\in S$, the resulting purchase probability $\pi(s)\in[0,1]$ and expected payment $e(s)$, and let $\sigma$ be an optimal buyer strategy in $\Gamma$: for every type $\theta$,
--   $$\theta\,\pi(\sigma(\theta))-e(\sigma(\theta)) \;\ge\; \theta\,\pi(s)-e(s)\qquad\text{for all } s\in S .$$
--   Then there is a direct mechanism $\Gamma'=(q,t)$ and an optimal buyer strategy $\sigma'$ in $\Gamma'$ such that
--
--   1. $\sigma'(\theta)=\theta$ for every $\theta\in[\underline\theta,\bar\theta]$, i.e. $\sigma'$ prescribes telling the truth;
--   2. for every $\theta\in[\underline\theta,\bar\theta]$, $q(\theta)=\pi(\sigma(\theta))$ and $t(\theta)=e(\sigma(\theta))$: the probability and payment under $\Gamma'$ equal the probability of purchase and the expected payment that result under $\Gamma$ when the buyer plays $\sigma$.
--
--   This justifies restricting the search for revenue-maximizing selling procedures to incentive-compatible direct mechanisms.
--
--   **Formalization Note** The book allows the seller to commit to an arbitrary extensive game and to her own strategy in it, and does not formalize a general mechanism. Here a mechanism is the reduced form the buyer faces: an arbitrary set $S$ of his strategies and, for each, the purchase probability and expected payment (all his expected utility depends on, by quasi-linearity and risk neutrality). $S$ is arbitrary, so direct mechanisms are a special case, not the hypothesis. An optimal strategy in a direct mechanism is required to map types into $[\underline\theta,\bar\theta]$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.10, Proposition 2.1

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.1 (Revelation Principle)**, p.10. For every (reduced-form) selling mechanism
`Γ` and every optimal buyer strategy `σ` in `Γ`, there is a direct mechanism `Γ′ = (q, t)` and an
optimal buyer strategy `σ′` in `Γ′` such that (i) `σ′(θ) = θ` for every `θ ∈ [θ̲, θ̄]`, and
(ii) for every `θ ∈ [θ̲, θ̄]`, `q(θ)` and `t(θ)` equal the probability of purchase and the expected
payment that result under `Γ` when the buyer plays `σ`. -/
theorem revelation_principle {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (Γ : Mechanism) (σ : ℝ → Γ.S) (hσ : Γ.IsOptimalStrategy θlo θhi σ) :
    ∃ (m : DirectMechanism θlo θhi) (σ' : ℝ → ℝ), m.IsOptimalStrategy σ' ∧
      (∀ θ ∈ Set.Icc θlo θhi, σ' θ = θ) ∧
      (∀ θ ∈ Set.Icc θlo θhi, m.q θ = Γ.prob (σ θ) ∧ m.t θ = Γ.pay (σ θ)) := by sorry

end MechanismDesign.Screening
