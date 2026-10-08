-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_eq_20_21
-- name    : MatroidProphetKW.Inter.eq_20_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:26:02.720189+00:00
-- url     : https://prove2.me/theorems/257c5a57-f180-4b44-9bb5-87b05843a912
-- title:
--   (20)–(21) — $w'(C_j(A)) + w'(R_j(A)) = \mathrm{OPT}(w') = w'(C(A)) + w'(R(A))$
-- statement:
--   Let $p \ge 1$, let $A \in \mathcal I$ be a feasible set and $w'$ any weight assignment. Then
--   $$w'(C_j(A)) + w'(R_j(A)) = \mathrm{OPT}(w') \quad \text{for every } j, \qquad w'(C(A)) + w'(R(A)) = \mathrm{OPT}(w').$$
--
--   These are the pointwise forms of (20) and (21): $C_j(A) \sqcup R_j(A)$ and $C(A) \sqcup R(A)$ are both partitions of the maximum-weight feasible set $B$. Taking expectations, and using that $w'$ has the same distribution as $w$, gives the paper's $\mathrm{OPT} = \mathbb E[w'(C_j(A)) + w'(R_j(A))]$ and $\mathrm{OPT} = \mathbb E[w'(C(A)) + w'(R(A))]$, which convert the three inequalities (22)–(24) into the bound of Proposition 3.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 17, Appendix A, (20)–(21)

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Equations (20)–(21) (Appendix A, p. 17), pointwise in the ghost weights `w′`: for every
`A ∈ ℐ`, `w′(C_j(A)) + w′(R_j(A)) = OPT(w′)` for all `j`, and
`w′(C(A)) + w′(R(A)) = OPT(w′)`. -/
theorem eq_20_21
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (hp : 0 < p) (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ)
    (A : Finset α) (hA : IsIndep M A) (w' : α → ℝ) :
    (∀ j, MatroidProphetKW.Single.wt w' (Cj M j A w') + MatroidProphetKW.Single.wt w' (Rj M j A w') = OPT M w') ∧
      MatroidProphetKW.Single.wt w' (Cint M A w') + MatroidProphetKW.Single.wt w' (Rint M A w') = OPT M w' := by sorry

end MatroidProphetKW.Inter
