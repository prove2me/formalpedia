-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_good_variable_reach_card
-- name    : KSATSingleFlip.Connect.good_variable_reach_card
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:31:25.772493+00:00
-- url     : https://prove2.me/theorems/3c238022-ab96-4b6a-a57d-33430fff3078
-- title:
--   Geometric bound for degree-truncated factor-graph reachability
-- statement:
--   For a finite formula whose clause scopes have cardinality at most $k$, retain an outgoing variable–clause incidence only when the departure variable has full-formula degree at most $D$. The number of variables reachable from any root in at most $r$ variable–clause–variable steps is at most $\sum_{i=0}^r(Dk)^i$. This is a supporting finite-graph bound for Lemma 2.7; it does not itself prove the lemma’s trimmed-ball or sensitivity claims.
-- source:
--   Auxiliary result for Lemma 2.7 of Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_GoodReach

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

theorem good_variable_reach_card {n : ℕ} (Φ : GFormula (Fin n)) (D k : ℕ)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (u : Fin n) (r : ℕ) :
    (goodVariableReach Φ D u r).card ≤ ∑ i ∈ Finset.range (r+1), (D*k)^i := by
  sorry

end KSATSingleFlip.Connect
