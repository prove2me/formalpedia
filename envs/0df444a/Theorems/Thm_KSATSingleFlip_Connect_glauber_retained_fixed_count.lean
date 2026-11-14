-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_glauber_retained_fixed_count
-- name    : KSATSingleFlip.Connect.glauber_retained_fixed_count
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:06:14.679009+00:00
-- url     : https://prove2.me/theorems/44b711af-2aba-4828-b0a7-690e631b0c81
-- title:
--   Retained-formula Glauber stationarity at fixed clause count
-- statement:
--   Fix an integer $M\ge0$ and draw an ordered formula of $M$ independent uniform proper clauses, and an independent uniform initial assignment $z$. Retain the clauses satisfied by $z$ and run any fixed number of Glauber steps on the retained formula from $z$. For every event of the retained ordered formula and final state, its probability equals the probability of the same event for the retained formula and $z$. This strengthens the Poisson-count statement in Lemma 7.8. If the finite clause sample space is empty, both finite averages use the formal model’s zero convention.
-- source:
--   Strengthening of Lemma 7.8, Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed p. 57 (PDF p. 59), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- The joint retained-formula/Glauber-state law is invariant at fixed clause count. -/
theorem glauber_retained_fixed_count {n k M : ℕ} (hn : 0 < n) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    uexp (fun z : Fin n → Bool => uexp (fun G : Fin M → ProperClause n k =>
      uprob (fun s : Fin t → Fin n × Bool =>
        let Φ0 := subF (ofList (List.ofFn G)) (satIdx (ofList (List.ofFn G)) z)
        P Φ0 (glauberState Φ0 z s)))) =
    uexp (fun z : Fin n → Bool => uprob (fun G : Fin M → ProperClause n k =>
      let Φ0 := subF (ofList (List.ofFn G)) (satIdx (ofList (List.ofFn G)) z)
      P Φ0 z)) := by
  sorry

end KSATSingleFlip.Connect
