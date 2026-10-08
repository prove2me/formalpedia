-- Prove2me | Theorems.Thm_MechanismDesign_Screening_ic_iff
-- name    : MechanismDesign.Screening.ic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:10.802676+00:00
-- url     : https://prove2.me/theorems/1ef20b2c-4868-4d01-8b5c-be9338d90b24
-- title:
--   Proposition 2.2 -- characterization of incentive-compatible direct mechanisms
-- statement:
--   Let $(q,t)$ be a direct mechanism on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, with $q$ valued in $[0,1]$. Then $(q,t)$ is incentive-compatible if and only if both
--
--   1. $q$ is (weakly) increasing on $[\underline\theta,\bar\theta]$, and
--   2. for every $\theta\in[\underline\theta,\bar\theta]$,
--   $$t(\theta)=t(\underline\theta)+\big(\theta q(\theta)-\underline\theta\, q(\underline\theta)\big)-\int_{\underline\theta}^{\theta} q(x)\,dx .$$
--
--   This is the complete description of the incentive-compatible direct mechanisms: they are parametrized by an increasing allocation rule and the lowest type's payment.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.14, Proposition 2.2

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.2**, p.14. A direct mechanism `(q, t)` is incentive-compatible if and only if
(i) `q` is increasing on `[θ̲, θ̄]`, and (ii) for every `θ ∈ [θ̲, θ̄]`,
`t(θ) = t(θ̲) + (θ q(θ) − θ̲ q(θ̲)) − ∫_{θ̲}^{θ} q(x) dx`. -/
theorem ic_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) :
    m.IsIC ↔
      (MonotoneOn m.q (Set.Icc θlo θhi) ∧
        ∀ θ ∈ Set.Icc θlo θhi,
          m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x) := by sorry

end MechanismDesign.Screening
