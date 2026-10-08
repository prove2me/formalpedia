-- Prove2me | Theorems.Thm_NegativeDP_Switching_theorem93
-- name    : NegativeDP.Switching.theorem93
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:22.059746+00:00
-- url     : https://prove2.me/theorems/533d6ae1-7a2c-43dd-9809-4e4441e7cf42
-- title:
--   Theorem 9.3 (N) — switching at each stage to the policy with the better continuation return does at least as well as both
-- statement:
--   Consider a negative dynamic programming problem: non-empty Borel state and action spaces $S,A$, a law of motion $q$, a return $r\le0$ with finite one-step expectations, and no discounting. Let $\sigma$ and $\tau$ be arbitrary (randomized, history-dependent) policies. For a history $h=(s_1,a_1,\dots,a_{n-1},s_n)$ let
--   $$u_n(h)=\sum_{j=n}^{\infty}\sigma_nq\cdots\sigma_jqr\,(h),\qquad v_n(h)=\sum_{j=n}^{\infty}\tau_nq\cdots\tau_jqr\,(h)$$
--   be the expected returns from stage $n$ on if $\sigma$, respectively $\tau$, is used from $h$ on, let $B_n=\{h: u_n(h)>v_n(h)\}$, and define $\pi$ by
--   $$\pi_n=\begin{cases}\sigma_n&\text{on }B_n,\\ \tau_n&\text{on }B_n^c.\end{cases}$$
--   Then this rule defines a policy, and
--   $$I(\pi)\ge\max\big(I(\sigma),I(\tau)\big)$$
--   at every initial state.
--
--   The policy $\pi$ chooses at each stage the policy that would be better if it were used for the whole remaining future. The theorem is an improvement routine valid for arbitrary history-dependent policies; Corollaries 9.1 and 9.2 (the Eaton–Zadeh theorem) are its Markov and stationary specialisations.
--
--   **Formalization Note** The paper states Theorem 9.3 for the discounted and negative cases; this item is the negative case. Lean's decision index $n$ is the paper's stage $n+1$. The statement has two parts: some plan satisfies the switching rule `IsSwitch P σ τ π` (the paper's "define $\pi$ by", which presupposes that $B_n$ is Borel so that $\pi_n$ is a kernel), and every plan satisfying it has the bound. Ties $u_n=v_n$ go to $\tau$, as printed. Returns lie in $[-\infty,0]$ and are computed in `EReal`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 888, Theorem 9.3

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

namespace NegativeDP.Switching

/-- Theorem 9.3 (N) (p. 888): the switching policy exists, and it does at least as well as
both `σ` and `τ` at every initial state. -/
theorem theorem93 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ : Plan (S := S) (A := A)) :
    (∃ π : Plan (S := S) (A := A), IsSwitch P σ τ π) ∧
    ∀ π : Plan (S := S) (A := A), IsSwitch P σ τ π →
      ∀ s, max (I P σ s) (I P τ s) ≤ I P π s := by sorry
end NegativeDP.Switching
