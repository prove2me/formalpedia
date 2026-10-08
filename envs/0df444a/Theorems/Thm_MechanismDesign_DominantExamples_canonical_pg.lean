-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_canonical_pg
-- name    : MechanismDesign.DominantExamples.canonical_pg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:27.710143+00:00
-- url     : https://prove2.me/theorems/afaa9f1a-8bdc-462a-b3a8-930638255b54
-- title:
--   Proposition 4.7 — canonical public good mechanisms are dominant strategy IC and ex post IR
-- statement:
--   Let $(q, t_1, \dots, t_N)$ be a canonical public good mechanism (Definition 4.4): for strictly increasing continuous $\psi_i$, the good is produced iff $\sum_i \psi_i(\theta_i) \ge c$, and when it is produced each agent pays the lowest type with which it would still have been produced. Then the mechanism is dominant strategy incentive-compatible and ex post individually rational, and for every agent $i$
--   $$u_i(\underline\theta,\theta_{-i}) = 0 \quad\text{for all } \theta_{-i} \in \Theta_{-i},$$
--   where $u_i(\theta) = \theta_i q(\theta) - t_i(\theta)$.
--
--   The decision rules of the second-best and profit-maximizing mechanisms of §3.3 are of this form, so they can be implemented in dominant strategies, although in general not with a balanced budget.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.88, Proposition 4.7

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.7, p.88. Every canonical public good mechanism is dominant strategy
incentive-compatible and ex post individually rational. Moreover, for every agent `i`,
`u_i(θ̲, θ_{-i}) = 0` for all `θ_{-i} ∈ Θ_{-i}`. -/
theorem canonical_pg {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by sorry

end MechanismDesign.DominantExamples
