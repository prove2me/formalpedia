-- Prove2me | Theorems.Thm_JewellMRP_Discounted_exists_optimal_stationary
-- name    : JewellMRP.Discounted.exists_optimal_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:03:42.581291+00:00
-- url     : https://prove2.me/theorems/4d9001b0-6b33-4471-8360-1f6d4898382d
-- title:
--   § The Optimal Policy with Discounting, p. 946 — among all policies of the infinite-step discounted problem there is an optimal stationary policy
-- statement:
--   Let a Markov-renewal program be given and let $\alpha > 0$. There is a stationary policy $d$ with return $v$ (the solution of (15) for $d$) such that for every nonstationary policy $\pi = (\pi_0, \pi_1, \dots)$, every vector of boundary rewards $V^0$ and every state $i$, the $n$-step return $V^\pi_i(n)$ converges as $n \to \infty$ to a limit $x$ with
--   $$
--   x \le v_i .
--   $$
--
--   The paper writes: "among all the optimal policies for the infinite-step or infinite-time discounted case, there exists an optimal, stationary policy". This is the statement that restricting attention to stationary policies, as the algorithm of Fig. 1 does, loses nothing.
--
--   **Formalization Note** Only the infinite-step case is formalized; the infinite-time case uses the continuous-time returns $v_i(t,\alpha)$ of (10), which are outside this mission. The comparison class is the paper's: deterministic Markov policies, possibly depending on the number of transitions made. The limit of the return of every such policy is asserted to exist, not assumed.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, pp. 946-947, The Optimal Policy with Discounting

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- § The Optimal Policy with Discounting, p. 946: in the infinite-step discounted problem there
is a stationary policy `d` whose return `v` (the solution of (15)) is at least the limiting
return of every, possibly nonstationary, policy, from every state and for all boundary
rewards. -/
theorem exists_optimal_stationary {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ (d : S → A) (v : S → ℝ), SolvesEval M α d v ∧
      ∀ (π : ℕ → S → A) (V0 : S → ℝ) (i : S), ∃ x : ℝ,
        Tendsto (fun n => policyReturn M α π V0 n i) atTop (𝓝 x) ∧ x ≤ v i := by sorry

end JewellMRP.Discounted
