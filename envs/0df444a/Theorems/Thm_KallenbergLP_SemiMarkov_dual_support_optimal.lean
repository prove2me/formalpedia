-- Prove2me | Theorems.Thm_KallenbergLP_SemiMarkov_dual_support_optimal
-- name    : KallenbergLP.SemiMarkov.dual_support_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:57.217873+00:00
-- url     : https://prove2.me/theorems/8f7b63e7-8633-41d4-ade7-7329d1fd3e67
-- title:
--   Theorem 7.2.3 — an optimal dual solution supports an optimal policy
-- statement:
--   Fix positive state weights $\beta_j>0$ and let $x^*$ maximize $\sum_{i,a}r^*_{ia}x_{ia}$ subject to $x_{ia}\geq0$ and
--
--   $$
--   \sum_i\sum_{a\in A(i)}(\delta_{ij}-p^*_{iaj})x_{ia}=\beta_j\qquad(j\in E).
--   $$
--
--   Any pure stationary policy $f_*^\infty$ whose chosen action has $x^*_{i,f_*(i)}>0$ in every state is optimal for the discounted semi-Markov model. The result extracts a policy from positive support of an optimal solution of program (7.2.11).
--
--   **Formalization Note** The dual variables are functions on all state-action pairs, but only available pairs occur in the constraints and objective.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 217, equation (7.2.11) and Theorem 7.2.3, https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.3. Every pure stationary action choice supported positively
by an optimal dual solution is an optimal policy. -/
theorem dual_support_optimal (M : Discounted S U) (β : S → ℝ)
    (hβ : ∀ i, 0 < β i) (x : S → U → ℝ) (hx : DualOptimal M β x)
    (f : S → U) (hf : ∀ i, f i ∈ M.model.actions i)
    (hpositive : ∀ i, 0 < x i (f i)) :
    ∀ i, policyValue M (purePolicy M f hf) i = value M i := by sorry

end KallenbergLP.SemiMarkov
