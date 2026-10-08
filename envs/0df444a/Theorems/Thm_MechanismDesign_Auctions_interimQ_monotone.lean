-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_interimQ_monotone
-- name    : MechanismDesign.Auctions.interimQ_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:26.953027+00:00
-- url     : https://prove2.me/theorems/7da477d7-1488-4c2a-bcfe-c09f5175b5e8
-- title:
--   Lemma 3.1 -- incentive compatibility makes each $Q_i$ increasing
-- statement:
--   Let $(q,t_1,\dots,t_N)$ be a direct mechanism in the single-unit auction environment, with interim allocation probabilities $Q_i$ and interim payments $T_i$.
--
--   **Lemma 3.1.** If the mechanism is incentive-compatible, then for every buyer $i$ the function $Q_i$ is (weakly) increasing on $[\underline\theta,\bar\theta]$:
--   $$\underline\theta \le \theta_i' \le \theta_i \le \bar\theta \implies Q_i(\theta_i') \le Q_i(\theta_i).$$
--
--   This is the monotonicity half of the characterization of Bayesian incentive compatibility (Proposition 3.2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.37, Lemma 3.1

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.1, p.37: in an incentive-compatible direct mechanism every interim allocation
probability `Q_i` is (weakly) increasing on `[θ̲, θ̄]`. -/
theorem interimQ_monotone {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) := by sorry

end MechanismDesign.Auctions
