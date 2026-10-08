-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_T_identity
-- name    : MatroidProphetKW.Inter.T_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:10.532059+00:00
-- url     : https://prove2.me/theorems/1a0f7945-a498-483e-99df-53e2a2728c8d
-- title:
--   §4.2 — the two expressions for $T(A,i,j)$ agree
-- statement:
--   Let $j$ be one of the matroids, $\alpha$ a real parameter, $A$ a set and $x_i$ an element with $A \cup \{x_i\} \in \mathcal I_j$. Then
--   $$\frac1\alpha\,\mathbb E\big[w'(R_j(A)) - w'(R_j(A \cup \{x_i\}))\big] = \frac1\alpha\,\mathbb E\big[w'(C_j(A \cup \{x_i\})) - w'(C_j(A))\big],$$
--   the expectations being over the ghost sample $w'$.
--
--   The two lines in the paper's definition of $T(A,i,j)$ therefore define the same number. The identity holds because $C_j(\cdot) \sqcup R_j(\cdot) = B$ for every independent argument; it is the first step of the telescoping proof of (13).
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 10, §4.2, definition of T(A, i, j)

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- The two expressions for `T(A, i, j)` in §4.2 (p. 10) agree:
`(1/α) E[w′(R_j(A)) − w′(R_j(A ∪ {x_i}))] = (1/α) E[w′(C_j(A ∪ {x_i})) − w′(C_j(A))]`
whenever `A ∪ {x_i} ∈ ℐ_j`. -/
theorem T_identity
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (a : ℝ) (j : Fin p) (A : Finset α) (x : α)
    (hAx : (M j).Indep (↑(insert x A) : Set α)) :
    Tij M F a j A x =
      (1 / a) * ∫ w', (MatroidProphetKW.Single.wt w' (Cj M j (insert x A) w') - MatroidProphetKW.Single.wt w' (Cj M j A w')) ∂(law F) := by sorry

end MatroidProphetKW.Inter
