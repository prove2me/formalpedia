-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_ic_iff
-- name    : MechanismDesign.Auctions.ic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:47.349164+00:00
-- url     : https://prove2.me/theorems/c373cd72-a224-482c-99d2-750044746932
-- title:
--   Proposition 3.2 -- characterization of Bayesian incentive compatibility
-- statement:
--   Let $(q,t_1,\dots,t_N)$ be a direct mechanism in the single-unit auction environment with interim allocation probabilities $Q_i$ and interim payments $T_i$.
--
--   **Proposition 3.2.** The mechanism is incentive-compatible if and only if for every buyer $i$:
--   1. $Q_i$ is increasing on $[\underline\theta,\bar\theta]$;
--   2. for every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$T_i(\theta_i) = T_i(\underline\theta) + \big(\theta_i Q_i(\theta_i) - \underline\theta\, Q_i(\underline\theta)\big) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx.$$
--
--   The seller's design problem therefore reduces to choosing an allocation rule with increasing interim probabilities and the interim payments of the lowest types.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.38, Proposition 3.2

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.2, p.38: a direct mechanism is incentive-compatible if and only if, for
every buyer `i`, `Q_i` is increasing on `[θ̲, θ̄]` and
`T_i(θ_i) = T_i(θ̲) + (θ_i Q_i(θ_i) − θ̲ Q_i(θ̲)) − ∫_{θ̲}^{θ_i} Q_i(x) dx` for every `θ_i`. -/
theorem ic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) :
    m.IsIC ↔ ∀ i, MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
          - ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions
