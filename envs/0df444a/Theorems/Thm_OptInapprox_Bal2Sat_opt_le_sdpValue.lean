-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_opt_le_sdpValue
-- name    : OptInapprox.Bal2Sat.opt_le_sdpValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:05.363143+00:00
-- url     : https://prove2.me/theorems/94fd3fb9-ce74-44c6-9ab4-e73824132b2c
-- title:
--   Proof of Thm 4, p. 21 — for a balanced instance, OPT ≤ SDP (the vector program relaxes OPT = max OBJ)
-- statement:
--   Let $I$ be a balanced weighted MAX-2SAT instance. Then its optimum is at most the value of the semidefinite relaxation:
--   $$
--   \mathrm{OPT} = \max_{x \in \{-1,1\}^n} \sum_{C=(r_ix_i\vee r_jx_j)} w_C\Bigl(\tfrac34 - \tfrac14 (r_ix_i)(r_jx_j)\Bigr) \;\le\; \mathrm{SDP} = \sup_{d,\ v_i \in \mathbb R^d,\ v_i\cdot v_i = 1} \sum_{C} w_C\Bigl(\tfrac34 - \tfrac14 (r_iv_i)\cdot(r_jv_j)\Bigr).
--   $$
--
--   This is the step "we directly relax this to a semidefinite program by replacing $x_i$ with a high-dimensional vector $v_i$, subject to $v_i\cdot v_i = 1$" of the proof of Theorem 4, and it gives the final inequality $\beta\,\mathrm{SDP} \ge \beta\,\mathrm{OPT}$.
--
--   **Formalization Note** Balancedness is needed because the relaxation is of the balanced form of the objective (without linear terms). The supremum ranges over unit-vector families in every finite dimension.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 21, §9, proof of Theorem 4 (OPT = max OBJ and its relaxation SDP)

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting

namespace OptInapprox.Bal2Sat

/-- Proof of Theorem 4, p. 21: for a balanced instance, `OPT = max OBJ` over `x ∈ {−1, 1}ⁿ` with
`OBJ = Σ_{C=(y∨z)} w_C (3/4 − y·z/4)`, and replacing each `xᵢ` by a unit vector `vᵢ` relaxes it
to the semidefinite program, so `OPT ≤ SDP`. -/
theorem opt_le_sdpValue {n : ℕ} (I : Instance n) (hbal : IsBalanced I) :
    OPT I ≤ sdpValue I := by sorry

end OptInapprox.Bal2Sat
