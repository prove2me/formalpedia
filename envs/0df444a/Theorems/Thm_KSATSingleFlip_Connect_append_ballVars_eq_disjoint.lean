-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_append_ballVars_eq_disjoint
-- name    : KSATSingleFlip.Connect.append_ballVars_eq_disjoint
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:48:42.514653+00:00
-- url     : https://prove2.me/theorems/e575dd88-82f6-40f4-a3ea-abcb7e73b90f
-- title:
--   Variable ball unaffected by a distant inserted clause
-- statement:
--   Let $\Phi$ be a finite formula, $C$ a clause, $v$ a variable, and $r$ a nonnegative integer. Suppose none of the variables of $C$ belongs to the variable vertices of the radius-$r$ factor-graph ball around $v$ in the enlarged formula $\Phi+[C]$. Then those variable vertices are unchanged by insertion: $$V(B_r(\Phi+[C],v))=V(B_r(\Phi,v)).$$ The ball includes its root even if that root is isolated. This is a supporting fact for the sensitivity estimate in Lemma 2.7.
-- source:
--   Auxiliary result for Lemma 2.7 of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem append_ballVars_eq_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (root : Fin n) (r : ℕ)
    (hno : Disjoint (vbl C) (ballVars (Φ ++ [C]) root r)) :
    ballVars (Φ ++ [C]) root r = ballVars Φ root r := by
  sorry

end KSATSingleFlip.Connect
