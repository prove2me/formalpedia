-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_append_ballVars_mono
-- name    : KSATSingleFlip.Connect.append_ballVars_mono
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:44:46.580238+00:00
-- url     : https://prove2.me/theorems/4aceb9d9-5ef4-4fd8-aece-003dd0b6e117
-- title:
--   Factor-graph balls grow under clause insertion
-- statement:
--   Let $\Phi$ be a finite formula, $C$ a clause, $v$ a variable, and $r$ a nonnegative integer. Let $V(B_r(\Phi,v))$ denote the variable vertices of the radius-$r$ factor-graph ball, including $v$ itself. Appending $C$ can only enlarge this variable set: $$V(B_r(\Phi,v))\subseteq V(B_r(\Phi+[C],v)).$$ Clause occurrences remain distinct. This is a supporting fact for the sensitivity estimate in Lemma 2.7.
-- source:
--   Auxiliary result for Lemma 2.7 of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem append_ballVars_mono {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (v : Fin n) (r : ℕ) : ballVars Φ v r ⊆ ballVars (Φ ++ [C]) v r := by
  sorry

end KSATSingleFlip.Connect
