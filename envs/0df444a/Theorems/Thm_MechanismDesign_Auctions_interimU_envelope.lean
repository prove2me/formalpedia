-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_interimU_envelope
-- name    : MechanismDesign.Auctions.interimU_envelope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:53.234488+00:00
-- url     : https://prove2.me/theorems/290877cd-6c66-4c7f-85ba-3b379d9330b5
-- title:
--   Lemma 3.2 -- $U_i$ is increasing and convex with $U_i' = Q_i$
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism in the single-unit auction environment, with interim utilities $U_i(\theta_i) = \theta_i Q_i(\theta_i) - T_i(\theta_i)$.
--
--   **Lemma 3.2.** For every buyer $i$:
--   1. $U_i$ is increasing on $[\underline\theta,\bar\theta]$;
--   2. $U_i$ is convex on $[\underline\theta,\bar\theta]$;
--   3. $U_i$ is differentiable at all but at most countably many points of $(\underline\theta,\bar\theta)$;
--   4. at every point $\theta_i \in (\underline\theta,\bar\theta)$ where $U_i$ is differentiable,
--   $$U_i'(\theta_i) = Q_i(\theta_i).$$
--
--   This envelope property is what pins down interim payoffs by the allocation rule (Lemma 3.3).
--
--   **Formalization Note** Differentiability and the derivative identity are stated at interior points. At an endpoint a two-sided derivative of the function on $\mathbb R$ depends on values outside the type interval, and the one-sided derivative need not equal $Q_i$ there (at $\underline\theta$ it is $\lim_{x\downarrow\underline\theta}Q_i(x)$, which can exceed $Q_i(\underline\theta)$); two points do not affect the countability claim.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.37, Lemma 3.2

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.2, p.37: in an incentive-compatible direct mechanism every interim utility `U_i` is
increasing and convex on `[θ̲, θ̄]`, differentiable at all but countably many interior points,
and `U_i'(θ_i) = Q_i(θ_i)` wherever it is differentiable. -/
theorem interimU_envelope {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimU i) (Set.Icc E.lo E.hi) ∧
    ConvexOn ℝ (Set.Icc E.lo E.hi) (m.interimU i) ∧
    {x | x ∈ Set.Ioo E.lo E.hi ∧ ¬ DifferentiableAt ℝ (m.interimU i) x}.Countable ∧
    ∀ x ∈ Set.Ioo E.lo E.hi, DifferentiableAt ℝ (m.interimU i) x →
      deriv (m.interimU i) x = m.interimQ i x := by sorry

end MechanismDesign.Auctions
