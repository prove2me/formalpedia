-- Prove2me | Theorems.Thm_KallenbergLP_Transient_transientPureStationary
-- name    : KallenbergLP.Transient.transientPureStationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:19:45.194159+00:00
-- url     : https://prove2.me/theorems/5a8ea7ec-eba5-4e37-b072-a38966e810b9
-- title:
--   Theorem 3.2.3 — a transient pure stationary policy exists
-- statement:
--   Consider a finite Markov decision model with state space $E$, admissible action sets $A(i)$ and substochastic transition numbers $p_{iaj}$. A policy $R$ is **transient** if $\sum_{t=1}^\infty P_R(X_t=j\mid X_1=i)<\infty$ for all $i,j\in E$.
--
--   If there exists a transient policy, then there also exists a transient pure and stationary policy:
--
--   $$\big(\exists R\in C:\ R\text{ transient}\big)\ \Longrightarrow\ \big(\exists f^\infty\in C_D:\ f^\infty\text{ transient}\big).$$
--
--   The hypothesis allows a history-dependent randomized policy; the conclusion produces a deterministic action $f(i)\in A(i)$ for each state, used at every epoch.
--
--   **Formalization Note** The statement involves no rewards. Section 3.2's standing Assumption 3.2.1 concerns rewards only, and the book's proof notes that the existence of a transient policy does not depend on them (it works with $r_{ia}=-1$, for which the assumption holds automatically), so no reward hypothesis is carried.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 40, Theorem 3.2.3

import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.3: if some policy is transient, some pure stationary policy is transient. -/
theorem transientPureStationary
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α)
    (h : ∃ R : Policy M, IsTransient M R) :
    ∃ f : PureRule M, IsTransient M (purePolicy M f) := by sorry

end KallenbergLP.Transient
