-- Prove2me | Theorems.Thm_MechanismDesign_Screening_revenue_equivalence
-- name    : MechanismDesign.Screening.revenue_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:06.692553+00:00
-- url     : https://prove2.me/theorems/3b926142-2654-4dab-8dd3-b0e664869162
-- title:
--   Lemma 2.4 -- Revenue Equivalence
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$. Then for all $\theta\in[\underline\theta,\bar\theta]$,
--   $$t(\theta)=t(\underline\theta)+\big(\theta q(\theta)-\underline\theta\, q(\underline\theta)\big)-\int_{\underline\theta}^{\theta} q(x)\,dx .$$
--
--   The payments of all types are pinned down by $q$ and the lowest type's payment $t(\underline\theta)$; this is the one-buyer form of the Revenue Equivalence Theorem of auction theory.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.13, Lemma 2.4

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.4 (Revenue Equivalence)**, p.13. For an incentive-compatible direct mechanism,
`t(θ) = t(θ̲) + (θ q(θ) − θ̲ q(θ̲)) − ∫_{θ̲}^{θ} q(x) dx` for all `θ ∈ [θ̲, θ̄]`. -/
theorem revenue_equivalence {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi,
      m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x := by sorry

end MechanismDesign.Screening
