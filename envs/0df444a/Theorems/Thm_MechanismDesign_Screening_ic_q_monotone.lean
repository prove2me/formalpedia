-- Prove2me | Theorems.Thm_MechanismDesign_Screening_ic_q_monotone
-- name    : MechanismDesign.Screening.ic_q_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:43:58.941199+00:00
-- url     : https://prove2.me/theorems/cf894ed1-a77f-439b-b3b0-f3dc1d83ab3c
-- title:
--   Lemma 2.1 -- incentive compatibility forces an increasing allocation
-- statement:
--   Let $(q,t)$ be a direct mechanism for types in $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$. If $(q,t)$ is incentive-compatible, then $q$ is (weakly) increasing on $[\underline\theta,\bar\theta]$:
--   $$\theta>\theta' \;\Longrightarrow\; q(\theta)\ge q(\theta').$$
--
--   This is the first of the two necessary conditions for incentive compatibility; Proposition 2.2 shows they are also sufficient.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.11, Lemma 2.1

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.1**, p.11. If a direct mechanism is incentive-compatible, then `q` is (weakly)
increasing in `θ` on `[θ̲, θ̄]`. -/
theorem ic_q_monotone {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.q (Set.Icc θlo θhi) := by sorry

end MechanismDesign.Screening
