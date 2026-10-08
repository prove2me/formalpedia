-- Prove2me | Theorems.Thm_KallenbergLP_Contracting_value_smallest_superharmonic
-- name    : KallenbergLP.Contracting.value_smallest_superharmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:35:23.862531+00:00
-- url     : https://prove2.me/theorems/5a019430-3a93-4c23-a866-716198697c00
-- title:
--   Theorem 3.4.1 — the value vector is the least superharmonic vector
-- statement:
--   In a finite contracting total-reward Markov decision model, let $v_i$ be the supremum of total expected reward from state $i$ over all history-dependent randomized policies. Then $v$ is TMD-superharmonic, and every TMD-superharmonic vector $w$ dominates it coordinatewise:
--
--   $$v_i\le w_i\qquad(i\in E).$$
--
--   This identifies the value vector without restricting the policy class to Markov or stationary policies.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 64, Theorem 3.4.1

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.1, p. 64. -/
theorem value_smallest_superharmonic
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M) :
    M.IsSuperharmonic M.value ∧
      ∀ w : E → ℝ, M.IsSuperharmonic w → ∀ i, M.value i ≤ w i := by sorry

end KallenbergLP.Contracting
