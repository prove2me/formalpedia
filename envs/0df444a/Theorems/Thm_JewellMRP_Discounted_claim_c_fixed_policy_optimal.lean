-- Prove2me | Theorems.Thm_JewellMRP_Discounted_claim_c_fixed_policy_optimal
-- name    : JewellMRP.Discounted.claim_c_fixed_policy_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:02:08.233709+00:00
-- url     : https://prove2.me/theorems/ff7c5392-6b34-4494-a5e6-4ede5b04e944
-- title:
--   Claim (c), p. 946 — if two successive policies are identical, no stationary policy has a higher return in any state
-- statement:
--   Let a Markov-renewal program be given and let $\alpha > 0$. Let $d$ be a stationary policy with return $v$ (the solution of (15) for $d$), and suppose the policy-improvement step of Fig. 1 applied to $d$ and $v$ returns $d$ itself. Then for every stationary policy $e$ with return $w$,
--   $$
--   w_i \le v_i \qquad \text{for every } i \in S .
--   $$
--
--   The paper writes: "(c) If two successive policies are identical, then the algorithm has converged on the optimal policy, in the sense that no other policy can lead to higher expected returns for any state $i$". This is the stopping criterion of Fig. 1.
--
--   **Formalization Note** "No other policy" is read as no other stationary policy: the section in which the claim appears concerns only stationary policies, and the next section of the paper introduces the comparison with nonstationary policies as "a slightly stronger result". That comparison is the separate milestone *§ The Optimal Policy with Discounting* and part of the goal.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 946, Claim (c)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (c), p. 946: if the policy-improvement step reproduces the policy `d`, then no
stationary policy has a higher return than `d` in any state. -/
theorem claim_c_fixed_policy_optimal {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : S → A} {v : S → ℝ}
    (hv : SolvesEval M α d v) (hfix : IsImprovement M α d v d)
    (e : S → A) (w : S → ℝ) (hw : SolvesEval M α e w) : ∀ i, w i ≤ v i := by sorry

end JewellMRP.Discounted
