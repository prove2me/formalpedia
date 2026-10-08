-- Prove2me | Theorems.Thm_MechanismDesign_Screening_ir_iff
-- name    : MechanismDesign.Screening.ir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:20.724004+00:00
-- url     : https://prove2.me/theorems/b7ff601c-1c33-4ee8-ad1a-6b2551f5f5e4
-- title:
--   Proposition 2.3 -- individual rationality reduces to the lowest type
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, with $u(\theta)=\theta q(\theta)-t(\theta)$. Then $(q,t)$ is individually rational if and only if
--   $$u(\underline\theta)\ge 0,$$
--   or equivalently, if and only if $t(\underline\theta)\le\underline\theta\, q(\underline\theta)$.
--
--   Together with Proposition 2.2 this describes the whole feasible set of the seller's problem.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.14, Proposition 2.3

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.3**, p.14. An incentive-compatible direct mechanism is individually rational
if and only if `u(θ̲) ≥ 0`, equivalently if and only if `t(θ̲) ≤ θ̲ q(θ̲)`. -/
theorem ir_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    (m.IsIR ↔ 0 ≤ m.u θlo) ∧ (m.IsIR ↔ m.t θlo ≤ θlo * m.q θlo) := by sorry

end MechanismDesign.Screening
