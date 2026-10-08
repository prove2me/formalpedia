-- Prove2me | Theorems.Thm_MechanismDesign_Screening_payoff_equivalence
-- name    : MechanismDesign.Screening.payoff_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:00.3824+00:00
-- url     : https://prove2.me/theorems/c18e9731-cae2-4220-bf3c-39e0d6d0851b
-- title:
--   Lemma 2.3 -- Payoff Equivalence
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, with $u(\theta)=\theta q(\theta)-t(\theta)$. Then for all $\theta\in[\underline\theta,\bar\theta]$,
--   $$u(\theta)=u(\underline\theta)+\int_{\underline\theta}^{\theta} q(x)\,dx .$$
--
--   The buyer's expected utilities are pinned down by $q$ and the lowest type's utility; any two mechanisms that induce the same $q$ and $u(\underline\theta)$ give every type the same payoff.
--
--   **Formalization Note** No measurability hypothesis is added: an incentive-compatible $q$ is monotone (Lemma 2.1) and bounded, hence integrable on every subinterval.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.12, Lemma 2.3

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.3 (Payoff Equivalence)**, p.12. For an incentive-compatible direct mechanism,
`u(θ) = u(θ̲) + ∫_{θ̲}^{θ} q(x) dx` for all `θ ∈ [θ̲, θ̄]`. -/
theorem payoff_equivalence {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi, m.u θ = m.u θlo + ∫ x in θlo..θ, m.q x := by sorry

end MechanismDesign.Screening
