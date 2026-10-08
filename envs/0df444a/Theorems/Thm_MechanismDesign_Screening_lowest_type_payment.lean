-- Prove2me | Theorems.Thm_MechanismDesign_Screening_lowest_type_payment
-- name    : MechanismDesign.Screening.lowest_type_payment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:23.827586+00:00
-- url     : https://prove2.me/theorems/e017e974-ec2c-468a-92e0-0947cd93e5a8
-- title:
--   Lemma 2.5 -- at a revenue-maximizing mechanism the lowest type gets zero utility
-- statement:
--   Let the buyer's type have a distribution with positive density $f$ on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$. Suppose the direct mechanism $(q,t)$ is incentive-compatible and individually rational and maximizes the seller's expected revenue $\int_{\underline\theta}^{\bar\theta} t(\theta)f(\theta)\,d\theta$ among all incentive-compatible, individually rational direct mechanisms. Then
--   $$t(\underline\theta)=\underline\theta\, q(\underline\theta).$$
--
--   With Proposition 2.2 this reduces the seller's problem to the choice of an increasing $q:[\underline\theta,\bar\theta]\to[0,1]$, with payments $t(\theta)=\theta q(\theta)-\int_{\underline\theta}^{\theta}q(x)\,dx$ (eq. (2.15)).
--
--   **Formalization Note** The comparison class (all incentive-compatible, individually rational direct mechanisms) is part of the hypothesis, as in the book. No integrability hypothesis is added: the payment rule of an incentive-compatible mechanism is bounded and measurable by Proposition 2.2, so its expected revenue is a genuine integral.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.15, Lemma 2.5

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.5**, p.15. If an incentive-compatible and individually rational direct mechanism
maximizes the seller's expected revenue among all incentive-compatible and individually rational
direct mechanisms, then `t(θ̲) = θ̲ q(θ̲)`. -/
theorem lowest_type_payment {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) (hir : m.IsIR)
    (hopt : ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
      expectedRevenue D m' ≤ expectedRevenue D m) :
    m.t θlo = θlo * m.q θlo := by sorry

end MechanismDesign.Screening
