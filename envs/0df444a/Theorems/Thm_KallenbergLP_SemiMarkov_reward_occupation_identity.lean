-- Prove2me | Theorems.Thm_KallenbergLP_SemiMarkov_reward_occupation_identity
-- name    : KallenbergLP.SemiMarkov.reward_occupation_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:57.63872+00:00
-- url     : https://prove2.me/theorems/9cf24373-92fc-467a-84d1-3547d909d26d
-- title:
--   Lemma 7.2.1 — discounted reward as occupation sum
-- statement:
--   Let $R$ be any history-dependent randomized policy and let $i$ be an initial state. For each epoch $n\geq1$, write $\pi_{iaj}(n,t,R)$ for the probability, conditional on $X_1=i$, that the current state-action pair is $(j,a)$ and the elapsed time before that epoch is at most $t$. Then
--
--   $$
--   v_i^\lambda(R)=\sum_{n=1}^{\infty}\sum_j\sum_{a\in A(j)}r^*_{ja}\int_0^\infty e^{-\lambda t}\,d\pi_{iaj}(n,t,R).
--   $$
--
--   Here $r^*_{ja}$ is the expected discounted reward earned during one epoch starting from $(j,a)$. This identity connects the original time-based expected reward to discounted state-action occupation weights.
--
--   **Formalization Note** Lean indexes the first epoch by $0$. Its `discountedVisit` is the Laplace–Stieltjes integral displayed above, evaluated by a finite-state recursion because decisions do not observe holding times.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 212–214, Lemma 7.2.1, https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Nonempty S] [Fintype U] [DecidableEq S] [DecidableEq U]

/-- Lemma 7.2.1. `discountedVisit` is the Laplace–Stieltjes integral of the
book's arrival-time distribution `π_{iaj}(n,t,R)`, with Lean epoch `n=0`
corresponding to printed epoch `n=1`. -/
theorem reward_occupation_identity (M : Discounted S U) (R : Policy M) (i : S) :
    policyValue M R i =
      ∑' n : ℕ, ∑ j : S, ∑ a ∈ M.model.actions j,
        rStar M j a * discountedVisit M R n [] i j a := by sorry

end KallenbergLP.SemiMarkov
