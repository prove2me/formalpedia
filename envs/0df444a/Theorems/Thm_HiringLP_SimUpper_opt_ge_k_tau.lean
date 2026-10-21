-- Prove2me | Theorems.Thm_HiringLP_SimUpper_opt_ge_k_tau
-- name    : HiringLP.SimUpper.opt_ge_k_tau
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:39.731581+00:00
-- url     : https://prove2.me/theorems/6ce811d4-0aea-402a-be0e-a1d31421701d
-- title:
--   App. D.7, p. ec19 — on the hard instance, offering to the k type-2 candidates gives OPT_sim ≥ kτ
-- statement:
--   Let $1 \le k \le j$ be integers, $\varepsilon > 0$ and $\tau \in (0,1)$, and let $I$ be the hard instance: $j^2$ type-1 candidates with $p_i = k/j$, $v_i = \tau + \varepsilon\tau/j$, and $k$ type-2 candidates with $p_i = 1$, $v_i = \tau$, with $k$ positions. Then
--   $$
--   \mathrm{OPT}_{\mathrm{sim}}(I) \ge k\tau .
--   $$
--
--   Sending offers to exactly the $k$ type-2 candidates hires all of them with certainty, fills the capacity without overage, and earns $k\tau$. This lower bound on the optimum is the denominator used in the proof of Theorem 4.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.7, p. ec19 (PDF p. 51), second paragraph

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_HardInstance

namespace HiringLP.SimUpper

/-- App. D.7, p. ec19: on the hard instance, offering to the `k` type-2 candidates earns `kτ`,
so `OPT_sim(I) ≥ kτ`. -/
theorem opt_ge_k_tau (k j : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (k : ℝ) * τ ≤ OPTsim (hardInstance k j ε τ) := by sorry

end HiringLP.SimUpper
