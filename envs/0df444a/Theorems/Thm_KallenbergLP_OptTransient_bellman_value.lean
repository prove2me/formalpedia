-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_bellman_value
-- name    : KallenbergLP.OptTransient.bellman_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:52:33.266291+00:00
-- url     : https://prove2.me/theorems/4dc07477-18c7-41b5-ad66-04729f143717
-- title:
--   Theorem 3.3.1 — finite transient value satisfies the functional equation
-- statement:
--   Assume at least one transient policy exists and that the transient value $w_i$, the supremum of total rewards over all transient policies from state $i$, is finite for every state. Then $w$ solves the Bellman functional equation:
--
--   $$
--   w_i=\max_{a\in A(i)}\left(r_{ia}+\sum_{j\in E}p_{iaj}w_j\right)\qquad(i\in E).
--   $$
--
--   The equation characterizes a necessary condition for the transient optimum. **Formalization Note** The finite maximum is expressed by an attaining action and upper bounds for all available actions.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 50, Theorem 3.3.1; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.1, printed p. 50: a finite transient value satisfies the Bellman equation. -/
theorem bellman_value {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hfin : ∀ i, BddAbove (transientValues m i)) :
    ∀ i : Fin n, ∃ a : {a : α // a ∈ m.actions i},
      optimalValue m i = m.reward i a.1 + ∑ j, m.transition i a.1 j * optimalValue m j ∧
      ∀ b : {b : α // b ∈ m.actions i},
        m.reward i b.1 + ∑ j, m.transition i b.1 j * optimalValue m j ≤ optimalValue m i := by sorry

end KallenbergLP.OptTransient
