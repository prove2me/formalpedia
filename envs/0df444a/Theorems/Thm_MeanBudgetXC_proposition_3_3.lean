-- Prove2me | Theorems.Thm_MeanBudgetXC_proposition_3_3
-- name    : MeanBudgetXC.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:37.105217+00:00
-- url     : https://prove2.me/theorems/00f925e7-ffb5-4e07-ba88-5f9d420a7073
-- title:
--   Proposition 3.3, Eq. (2) — eliminating the singleton means
-- statement:
--   Let $3\le d\le N$, so that the standing assumptions of Section 3.2 hold with activity two, and let $T_i(q)$ be the sum of the $d-1$ largest pair coordinates incident to $i$ and $F_S(q)=\sum_{i\in S}T_i(q)-q(E(S))$. For every $B\ge0$,
--   $$P_B=\Big\{q\ge0:\ \sum_iT_i(q)\le B,\ \ F_S(q)\le1\ (|S|=d)\Big\}.$$
--
--   This describes the budgeted body in the pair coordinates alone. The remaining difficulty is the number of inequalities $F_S(q)\le1$.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Proposition 3.3, display (2), p.11

import Mathlib
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_contextValue

namespace MeanBudgetXC

/-- **Proposition 3.3**, display (2) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for
Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 3.2, p.11).
Under the standing assumptions of Section 3.2 (activity two, `3 ≤ d ≤ N`), for every `B ≥ 0` the
budgeted pair projection is
`P_B = {q ≥ 0 : ∑_i T_i(q) ≤ B, F_S(q) ≤ 1 (|S| = d)}`.

**Formalization Note** The vertex set is a generic finite type `V` with `N = card V`. -/
theorem proposition_3_3 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd3 : 3 ≤ d)
    (hdN : d ≤ Fintype.card V) (B : ℝ) (hB : 0 ≤ B) :
    budgetBody V d 2 B =
      {q | (∀ e, 0 ≤ q e) ∧ ∑ i, topSum d q i ≤ B ∧
        ∀ S : Finset V, S.card = d → contextValue d q S ≤ 1} := by sorry

end MeanBudgetXC
