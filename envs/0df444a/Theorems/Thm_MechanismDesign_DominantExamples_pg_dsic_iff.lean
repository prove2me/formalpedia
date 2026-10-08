-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_pg_dsic_iff
-- name    : MechanismDesign.DominantExamples.pg_dsic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:21.259559+00:00
-- url     : https://prove2.me/theorems/c0ab1425-213f-40ea-b2ba-de9bb7918c46
-- title:
--   Proposition 4.5 — dominant strategy IC public good mechanisms are threshold rules
-- statement:
--   A deterministic direct public good mechanism $(q, t_1, \dots, t_N)$ on $\Theta = [\underline\theta,\bar\theta]^I$ is dominant strategy incentive-compatible if and only if for every agent $i$ and every $\theta_{-i} \in \Theta_{-i}$ there are a number $\hat\theta_i \in \mathbb R$ and two payments $\tau_i, \hat\tau_i \in \mathbb R$ such that for every $\theta_i \in [\underline\theta,\bar\theta]$:
--
--   1. $\theta_i < \hat\theta_i \Rightarrow q(\theta_i,\theta_{-i}) = 0$ and $t_i(\theta_i,\theta_{-i}) = \tau_i$;
--   2. $\theta_i > \hat\theta_i \Rightarrow q(\theta_i,\theta_{-i}) = 1$ and $t_i(\theta_i,\theta_{-i}) = \hat\tau_i$;
--   3. $\theta_i = \hat\theta_i \Rightarrow$ either $q(\theta_i,\theta_{-i}) = 0$ and $t_i(\theta_i,\theta_{-i}) = \tau_i$, or $q(\theta_i,\theta_{-i}) = 1$ and $t_i(\theta_i,\theta_{-i}) = \hat\tau_i$;
--
--   and
--   $$\hat\tau_i - \tau_i = \hat\theta_i.$$
--
--   The threshold $\hat\theta_i$ and the payments may depend on $\theta_{-i}$, and $\hat\theta_i$ may lie outside $[\underline\theta,\bar\theta]$, in which case agent $i$'s report never affects the decision. This characterization is the main tool for the budget-balance results of §4.3.5.
--
--   **Formalization Note** The existential quantifier sits inside the quantifier over $\theta_{-i}$, as on the page, and $\hat\theta_i$ ranges over all of $\mathbb R$ (footnote 3 of Chapter 4).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.86, Proposition 4.5 (and footnote 3, p.236)

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.5, p.86. A direct public good mechanism is dominant strategy
incentive-compatible if and only if for every agent `i` and every `θ_{-i} ∈ Θ_{-i}`
(represented by `θ ∈ Θ`, whose `i`-th coordinate is overwritten) there are a real number
`θ̂_i` (possibly outside `[θ̲, θ̄]`) and two payments `τ_i, τ̂_i ∈ ℝ` such that for all
`θ_i ∈ [θ̲, θ̄]`:
`θ_i < θ̂_i ⇒ q(θ_i, θ_{-i}) = 0 and t_i(θ_i, θ_{-i}) = τ_i`;
`θ_i > θ̂_i ⇒ q(θ_i, θ_{-i}) = 1 and t_i(θ_i, θ_{-i}) = τ̂_i`;
`θ_i = θ̂_i ⇒ (q = 0 and t_i = τ_i) or (q = 1 and t_i = τ̂_i)`;
and `τ̂_i − τ_i = θ̂_i`. -/
theorem pg_dsic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι, ∃ θhat τ τhat : ℝ,
      (∀ x ∈ Set.Icc E.lo E.hi, x < θhat →
        M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, θhat < x →
        M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, x = θhat →
        (M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∨
        (M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat)) ∧
      τhat - τ = θhat := by sorry

end MechanismDesign.DominantExamples
