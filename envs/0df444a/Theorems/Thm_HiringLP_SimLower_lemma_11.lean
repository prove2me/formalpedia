-- Prove2me | Theorems.Thm_HiringLP_SimLower_lemma_11
-- name    : HiringLP.SimLower.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:26.12072+00:00
-- url     : https://prove2.me/theorems/2dd4f270-70b2-4f77-8f9b-d23690936920
-- title:
--   Lemma 11 — some optimal solution of LP_sim is a filled prefix in value order
-- statement:
--   Let $I=(k,n,p,v)$ be a valid Simultaneous Offering instance, with candidates labelled so that $v_1\ge\dots\ge v_n$. Then there is an optimal solution $(y,z)$ of $\mathrm{LP}_{\mathrm{sim}}(I)$ and an index $j$ such that
--   $$y_i=1\ (1\le i\le j-1),\qquad y_j>0,\qquad y_i=0\ (j+1\le i\le n).$$
--
--   For fixed $z$ the LP is a fractional knapsack problem, and this is the structure of its greedy solutions. It lets an optimal LP solution be read as a randomisation between two value-ordered policies.
--
--   **Formalization Note** Indices are 0-based: $y_i=1$ for $i<j$, $y_j>0$, $y_i=0$ for $i>j$ (`IsPrefix y j`). A valid instance has $n\ge k\ge1$, so an index exists.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 27, Lemma 11

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP

namespace HiringLP.SimLower

/-- Lemma 11 (p. 27): some optimal solution `(y, z)` of `LP_sim(I)` has the prefix structure
`yᵢ = 1` for `i < j`, `y_j > 0`, `yᵢ = 0` for `i > j` (0-based `j`; labels sorted by value). -/
theorem lemma_11 {n : ℕ} (I : SimInstance n) (hI : I.Valid) :
    ∃ (y : Fin n → ℝ) (z : ℝ), IsLPOpt I y z ∧ ∃ j : Fin n, IsPrefix y j := by sorry

end HiringLP.SimLower
