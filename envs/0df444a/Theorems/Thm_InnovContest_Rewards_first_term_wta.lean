-- Prove2me | Theorems.Thm_InnovContest_Rewards_first_term_wta
-- name    : InnovContest.Rewards.first_term_wta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:25.709555+00:00
-- url     : https://prove2.me/theorems/3a2dc905-6186-4717-b937-8d46b67e49cc
-- title:
--   Proof of Theorem 2 — winner take all strictly maximizes expected best performance
-- statement:
--   Suppose $c_p>0$ and $c_p<B<n c_p$. Let $r^{\mathrm{WTA}}=(B,0,\ldots,0)$ be the winner-take-all allocation. Every other feasible allocation $r$ yields strictly less expected best participating submission:
--
--   $$\mathbb E[\text{best submission under }r]<\mathbb E[\text{best submission under }r^{\mathrm{WTA}}].$$
--
--   The entry threshold and equilibrium performance are recalculated under each allocation. This is the performance half of the design comparison; the strict form isolates winner-take-all at zero failure cost.
--
--   **Formalization Note** The source states maximization without an explicit strictness qualifier. Strictness is the corrected strengthening needed for the source's conclusion about every optimum.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. 28, Proof of Theorem 2, first-term maximization claim (strict strengthening)

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- The strict version of the first-term claim in the proof of Theorem 2, p. 28. -/
theorem first_term_wta (M : AbilityModel) (budget cp : ℝ)
    (hcp : 0 < cp) (hbudget : cp < budget)
    (hupper : budget < (M.n : ℝ) * cp)
    (r : ℕ → ℝ) (hr : Feasible M.n budget r)
    (hne : r ≠ equalSplit budget 1) :
    bestExpected M r cp < bestExpected M (equalSplit budget 1) cp := by sorry

end InnovContest.Rewards
