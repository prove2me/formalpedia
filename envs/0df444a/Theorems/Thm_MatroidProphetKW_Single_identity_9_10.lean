-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_identity_9_10
-- name    : MatroidProphetKW.Single.identity_9_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:29.654258+00:00
-- url     : https://prove2.me/theorems/5a63e6d0-939d-47f6-9e15-76bda841d7b5
-- title:
--   §3.3 display — $w'(C(A)) + w'(R(A)) = w'(B)$, so (9) = (10)
-- statement:
--   Let $\mathcal M$ be a matroid, $w' \ge 0$ a weight assignment, $B$ the maximum-weight basis for $w'$, and $C(\cdot)$, $R(\cdot)$ the sets of §3.2. For every set $A$ and element $x$ with $A \cup \{x\} \in \mathcal I$,
--   $$w'(C(A)) + w'(R(A)) = w'(B) = w'(C(A \cup \{x\})) + w'(R(A \cup \{x\})),$$
--   and consequently
--   $$w'(R(A)) - w'(R(A \cup \{x\})) = w'(C(A \cup \{x\})) - w'(C(A)).$$
--
--   Taking expectations shows that the two formulas (9) and (10) for the threshold $T_i$ (with $A = A_{i-1}$, $x = x_i$) define the same value.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 7, §3.3, display after (9)–(10)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

/-- The identity (9) = (10) (Kleinberg–Weinberg, arXiv:1201.4764v1, §3.3, p. 7): with `B` the
maximum-weight basis for `w′`, for every independent `A ∪ {x}`,
  `w′(C(A)) + w′(R(A)) = w′(B) = w′(C(A ∪ {x})) + w′(R(A ∪ {x}))`, hence
  `w′(R(A)) − w′(R(A ∪ {x})) = w′(C(A ∪ {x})) − w′(C(A))`. -/
theorem identity_9_10 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (A : Finset α) (x : α) (hAx : M.Indep (↑(insert x A) : Set α)) :
    (wt w' (Cset M A w') + wt w' (Rset M A w') = wt w' (maxBase M w') ∧
      wt w' (maxBase M w') = wt w' (Cset M (insert x A) w') + wt w' (Rset M (insert x A) w')) ∧
    wt w' (Rset M A w') - wt w' (Rset M (insert x A) w')
      = wt w' (Cset M (insert x A) w') - wt w' (Cset M A w') := by sorry

end MatroidProphetKW.Single
