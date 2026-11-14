-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_ballClauseLabels_eq_disjoint
-- name    : KSATSingleFlip.Connect.ballClauseLabels_eq_disjoint
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:51:41.033242+00:00
-- url     : https://prove2.me/theorems/ccac8c5d-9f72-4453-adf4-2700c59bee01
-- title:
--   Clause labels in a ball are unaffected by a distant insertion
-- statement:
--   Let $\Phi$ be a finite formula, $C$ a clause, $v$ a variable, and $r$ a nonnegative integer. If the variables of $C$ are disjoint from the variable vertices of the radius-$r$ factor-graph ball around $v$ in $\Phi+[C]$, then the set of original clause-occurrence labels in that ball is unchanged by insertion. Repeated clauses have distinct occurrence labels. This supports the sensitivity estimate in Lemma 2.7.
-- source:
--   Auxiliary result for Lemma 2.7 of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem ballClauseLabels_eq_disjoint {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (root : Fin n) (r : ℕ) (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballClauseLabels (Φ ++ [C]) root r = ballClauseLabels Φ root r := by
  sorry

end KSATSingleFlip.Connect
