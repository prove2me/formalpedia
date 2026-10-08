-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_payoff_equivalence
-- name    : MechanismDesign.Auctions.payoff_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:38.020233+00:00
-- url     : https://prove2.me/theorems/cfdba33b-ae16-4316-b2b1-01717bedd719
-- title:
--   Lemma 3.3 -- payoff equivalence
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism in the single-unit auction environment with interim allocation probabilities $Q_i$ and interim utilities $U_i$.
--
--   **Lemma 3.3 (Payoff Equivalence).** For every buyer $i$ and every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$U_i(\theta_i) = U_i(\underline\theta) + \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx.$$
--
--   Interim payoffs of all types are thus determined by the interim allocation rule and the payoff of the lowest type.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.37, Lemma 3.3

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.3 (Payoff Equivalence), p.37:
`U_i(θ_i) = U_i(θ̲) + ∫_{θ̲}^{θ_i} Q_i(x) dx` in every incentive-compatible direct mechanism. -/
theorem payoff_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimU i x = m.interimU i E.lo + ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions
