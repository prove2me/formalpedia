-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_degree_append_one
-- name    : KSATSingleFlip.Connect.degree_append_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:43:11.787199+00:00
-- url     : https://prove2.me/theorems/397ac1ec-4d4d-4a6d-b978-c117ff7082b2
-- title:
--   Change in variable degree upon insertion of a clause
-- statement:
--   For a finite formula $\Phi$, a clause $C$, and a variable $u$, appending $C$ changes the full-formula degree of $u$ by exactly one if $u$ occurs in $C$, and leaves it unchanged otherwise: $$\deg_{\Phi\mathbin{+}[C]}(u)=\deg_\Phi(u)+\mathbf{1}_{\{u\in\operatorname{vbl}(C)\}}.$$ Clause occurrences are counted with multiplicity. This is a supporting fact for the sensitivity part of Lemma 2.7.
-- source:
--   Auxiliary result for Lemma 2.7 of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem degree_append_one {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (u : Fin n) :
    degree (Φ ++ [C]) u = degree Φ u + if u ∈ vbl C then 1 else 0 := by
  sorry

end KSATSingleFlip.Connect
