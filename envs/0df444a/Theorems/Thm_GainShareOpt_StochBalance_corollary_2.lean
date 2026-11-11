-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_corollary_2
-- name    : GainShareOpt.StochBalance.corollary_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:30.377366+00:00
-- url     : https://prove2.me/theorems/6fcfa626-11ed-4db5-89d7-f1dd6a6b44a1
-- title:
--   Corollary 2 — validated endpoint enclosure: $q(a)>a$, $q(b)<b$, $\gamma^*\in[0.5802,0.5805]$
-- statement:
--   With $a=0.5802$ and $b=0.5805$, the exact return values satisfy
--   $$q(a)\in[0.5803315,\,0.5805316],\qquad q(b)\in[0.5801332,\,0.5803333].$$
--   In particular $q(a)>a$ and $q(b)<b$, and the optimal value of Program (31) satisfies $\gamma^*\in[0.5802,0.5805]$.
--
--   Through Theorem 6 this gives the enclosure of Theorem 3.
--
--   Differences from the source:
--   - encoding: decimal endpoints 0.5803315, …, 0.5805 → exact rationals (e.g. 5803315/10^7, 2901/5000); reason: same numbers
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 65, Corollary 2

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra
import Definitions.Def_GainShareOpt_StochBalance_NodalCert

namespace GainShareOpt.StochBalance

/-- Corollary 2 (validated endpoint enclosure). -/
theorem corollary_2 :
    returnValue endA ∈ Set.Icc (5803315 / 10 ^ 7 : ℝ) (5805316 / 10 ^ 7) ∧
    returnValue endB ∈ Set.Icc (5801332 / 10 ^ 7 : ℝ) (5803333 / 10 ^ 7) ∧
    endA < returnValue endA ∧ returnValue endB < endB ∧
    gammaStar ∈ Set.Icc endA endB := by sorry

end GainShareOpt.StochBalance
