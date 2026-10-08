-- Prove2me | Theorems.Thm_MyersonBargaining_NashSolution_conflict_payoff_in_FStar
-- name    : MyersonBargaining.NashSolution.conflict_payoff_in_FStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:27.227963+00:00
-- url     : https://prove2.me/theorems/9f358b1f-443c-40c2-b689-185388568427
-- title:
--   Section 5 — the conflict payoff is incentive-feasible
-- statement:
--   Fix a conflict choice $c^*\in C$ in a finite Bayesian collective choice problem. The direct mechanism that always selects $c^*$ is a choice mechanism and is Bayesian incentive-compatible. Its interim payoff vector equals the conflict vector $t$, where
--
--   $$
--   t_{i,a_i}=\sum_\alpha P_i(\alpha\mid a_i)U_i(c^*,\alpha).
--   $$
--
--   Consequently $t\in F^*$. This gives the individually rational set $F^*_+$ a feasible reference point.
--
--   **Formalization Note** The constant mechanism is $\pi(c\mid\alpha)=1$ if $c=c^*$ and $0$ otherwise. The conflict vector $t$ is defined by the displayed formula (16), not as the payoff of this mechanism; that the two agree is the third conjunct, and $t\in F^*$ the fourth.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 68, Section 5, after Eq. (16)

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Section 5, p. 68: constant conflict choice generates an incentive-feasible payoff. -/
theorem conflict_payoff_in_FStar (G : Problem ι A C) (cstar : C) :
    IsChoiceMechanism (constMech (A := A) cstar) ∧
    IsBIC G (constMech (A := A) cstar) ∧
    V G (constMech (A := A) cstar) = conflictPayoff G cstar ∧
    conflictPayoff G cstar ∈ FStar G := by sorry

end MyersonBargaining.NashSolution
