-- Prove2me | Theorems.Thm_InnovContest_Rewards_existence
-- name    : InnovContest.Rewards.existence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:12.305307+00:00
-- url     : https://prove2.me/theorems/6df7c128-c4c7-42d3-98c6-e289ca2e8863
-- title:
--   Proof of Theorem 2 (Existence) — an optimal allocation exists
-- statement:
--   For a positive budget $B$ and nonnegative participation and failure costs $c_p,c_f$, the firm's expected objective over feasible reward allocations attains a maximum:
--
--   $$\exists r^*\in\mathcal R_B\quad\forall r\in\mathcal R_B,\quad \Pi(r;c_p,c_f)\le\Pi(r^*;c_p,c_f).$$
--
--   This existence claim makes the optimal design theorem substantive, including when the best objective value is negative.
--
--   **Formalization Note** The feasible set uses the paper's budget inequality. The nonnegative-objective restriction introduced only in the printed proof is excluded.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. 28, Proof of Theorem 2 (Existence), corrected to the stated problem

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Existence claim in the proof of Theorem 2, p. 28, for the paper's stated objective and
budget inequality. The proof's additional nonnegative-objective constraint is omitted. -/
theorem existence (M : AbilityModel) (budget cp cf : ℝ)
    (hbudget : 0 < budget) (hcp : 0 ≤ cp) (hcf : 0 ≤ cf) :
    ∃ r : ℕ → ℝ, IsOptimal M budget cp cf r := by sorry

end InnovContest.Rewards
