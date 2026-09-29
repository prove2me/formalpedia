-- Prove2me | Theorems.Thm_GKP1998_besselK_decay_besselI_growth
-- name    : GKP1998.besselK_decay_besselI_growth
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:45:34.465429+00:00
-- url     : https://prove2.me/theorems/df2165ba-ec2d-414d-b450-f2a9610b81e5
-- title:
--   Regularity at the horizon: $K_\nu$ decays and $I_\nu$ grows exponentially
-- statement:
--   For every real $\nu\ge0$: (a) there is a constant $C$ with $|K_\nu(x)|\le Ce^{-x}$ for all $x\ge1$; (b) there is $c>0$ with $e^{-cx}I_\nu(x)\to+\infty$ as $x\to+\infty$. This is the reason given after Eq. (23) for keeping $K_\nu$ rather than $I_\nu$.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 109, text following Eq. (23)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Text after Eq. (23): regularity at the horizon selects `K_ν` over `I_ν` because `K_ν`
falls off exponentially for large argument while `I_ν` grows exponentially. -/
theorem besselK_decay_besselI_growth (ν : ℝ) (hν : 0 ≤ ν) :
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |besselK ν x| ≤ C * Real.exp (-x)) ∧
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun x => Real.exp (-c * x) * besselI ν x) atTop atTop) := by sorry
end GKP1998
