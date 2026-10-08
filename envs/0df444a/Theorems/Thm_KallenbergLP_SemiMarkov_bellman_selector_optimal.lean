-- Prove2me | Theorems.Thm_KallenbergLP_SemiMarkov_bellman_selector_optimal
-- name    : KallenbergLP.SemiMarkov.bellman_selector_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:58.948056+00:00
-- url     : https://prove2.me/theorems/188aea32-0fcd-4e2d-bc42-d516cfeeb01c
-- title:
--   Theorem 7.2.2 — a Bellman equality selector is optimal
-- statement:
--   Choose an available action $a_i\in A(i)$ in each state. If this choice attains the discounted Bellman value,
--
--   $$
--   r^*_{ia_i}+\sum_jp^*_{ia_i j}v^\lambda_j=v^\lambda_i\qquad(i\in E),
--   $$
--
--   then the pure stationary policy $f^\infty$ defined by $f(i)=a_i$ has discounted reward $v^\lambda$ at every initial state. Thus a statewise equality selector is optimal among all policies in the DRD model.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 216, Theorem 7.2.2, https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.2. Any pure stationary selector attaining the Bellman value
at every state is optimal among all history-dependent randomized policies. -/
theorem bellman_selector_optimal (M : Discounted S U) (f : S → U)
    (hf : ∀ i, f i ∈ M.model.actions i)
    (hbellman : ∀ i, rStar M i (f i) +
      ∑ j, pStar M i (f i) j * value M j = value M i) :
    ∀ i, policyValue M (purePolicy M f hf) i = value M i := by sorry

end KallenbergLP.SemiMarkov
