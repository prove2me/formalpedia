-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_revenue_equivalence
-- name    : MechanismDesign.Auctions.revenue_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:36.833608+00:00
-- url     : https://prove2.me/theorems/94729ab5-5328-402b-876c-0b9d8fa87444
-- title:
--   Lemma 3.4 -- revenue equivalence
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism in the single-unit auction environment with interim allocation probabilities $Q_i$ and interim payments $T_i$.
--
--   **Lemma 3.4 (Revenue Equivalence).** For every buyer $i$ and every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$T_i(\theta_i) = T_i(\underline\theta) + \big(\theta_i Q_i(\theta_i) - \underline\theta\, Q_i(\underline\theta)\big) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx.$$
--
--   Interim payments are therefore determined by the interim allocation rule and the payment of the lowest type; in particular two mechanisms with the same $Q_i$ and the same $T_i(\underline\theta)$ raise the same expected revenue.
--
--   **Formalization Note** The printed formula reads $\underline\theta_i Q_i((\underline\theta_i))$ for the subtracted term; the doubled parenthesis is a typo, and $\underline\theta_i = \underline\theta$ because all buyers share the support. The statement uses $\underline\theta\, Q_i(\underline\theta)$, as in Proposition 3.2 (ii).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.37, Lemma 3.4

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.4 (Revenue Equivalence), p.37:
`T_i(θ_i) = T_i(θ̲) + (θ_i Q_i(θ_i) − θ̲ Q_i(θ̲)) − ∫_{θ̲}^{θ_i} Q_i(x) dx` in every
incentive-compatible direct mechanism. -/
theorem revenue_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
        - ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions
