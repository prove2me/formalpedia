-- Prove2me | Theorems.Thm_JewellMRP_Discounted_claim_b_strict_improvement
-- name    : JewellMRP.Discounted.claim_b_strict_improvement
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:01:39.053985+00:00
-- url     : https://prove2.me/theorems/d4969f8a-5f03-4e6e-89ae-e4f7ec52d141
-- title:
--   Claim (b), p. 946 — a change of policy in the improvement step strictly increases the return of some state and decreases none
-- statement:
--   Let a Markov-renewal program be given and let $\alpha > 0$. Let $d$ be a stationary policy with return $v$ (the solution of (15) for $d$), let $d'$ be obtained from $d$ and $v$ by the policy-improvement step of Fig. 1, with $d' \ne d$, and let $v'$ be the return of $d'$. Then
--   $$
--   v_i \le v'_i \ \text{ for every } i \in S, \qquad\text{and}\qquad v_i < v'_i \ \text{ for some } i \in S .
--   $$
--
--   The paper writes: "(b) The policy-determining step strictly increases the expected return of at least one state in each cycle of the algorithm, if there was an improvement in the test quantity that led to the change in policy". Under the retention rule of Fig. 1 the policy changes exactly when the test quantity strictly improves in some state, which is the hypothesis $d' \ne d$. The argument the paper refers to (Howard's) gives both that no state's return decreases and that at least one strictly increases, and both are stated. This monotonicity is what prevents the algorithm from revisiting a policy.
--
--   **Formalization Note** Returns are the solutions of (15), which exist and are unique by Claim (a).
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 946, Claim (b)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (b), p. 946: if the policy-improvement step changes the policy `d` into `d' ≠ d`,
then the return of `d'` is at least that of `d` in every state and strictly greater in at
least one state. -/
theorem claim_b_strict_improvement {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d d' : S → A} {v v' : S → ℝ}
    (hv : SolvesEval M α d v) (hv' : SolvesEval M α d' v')
    (himp : IsImprovement M α d v d') (hne : d' ≠ d) :
    (∀ i, v i ≤ v' i) ∧ ∃ i, v i < v' i := by sorry

end JewellMRP.Discounted
