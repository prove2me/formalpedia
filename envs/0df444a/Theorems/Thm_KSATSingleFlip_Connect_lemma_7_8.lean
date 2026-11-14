-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_8
-- name    : KSATSingleFlip.Connect.lemma_7_8
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:14:56.965905+00:00
-- url     : https://prove2.me/theorems/324df13f-66bd-4634-a4c1-44d5c9f4bbe1
-- title:
--   Lemma 7.8 — Joint stationarity of retained formula and Glauber state
-- statement:
--   Title: Lemma 7.8 — Joint stationarity of the retained formula and Glauber state
--
--   Let n > 0, m ≥ 0, and t ≥ 0. Sample a Poisson random proper k-SAT formula Φ⁺ with mean m and an independent uniform assignment z. Let Φ₀ consist of the clause occurrences of Φ⁺ satisfied by z, in their original order, and let Xₜ be the state after t independent uniformly sampled Glauber updates on Φ₀ from z. Then (Φ₀, Xₜ) and (Φ₀, z) have the same joint law.
--
--   The formal statement tests equality on every event of an ordered clause list and an assignment, preserving repeated clause occurrences. It assumes n > 0 so the uniformly selected update variable exists.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, Lemma 7.8, printed p. 57 (PDF p. 59 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Lemma 7.8, printed p. 57 (PDF p. 59), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.8: with a uniform initial assignment, the joint law of the
retained formula and the Glauber state is invariant at every fixed time. -/
theorem lemma_7_8 {n k : ℕ} (hn : 0 < n) (m : ℝ) (hm : 0 ≤ m) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    uexp (fun z : Fin n → Bool =>
      poisExp (allClauses n k) m (fun l =>
        uprob fun s : Fin t → Fin n × Bool =>
          let Φ0 := subF (ofList l) (satIdx (ofList l) z)
          P Φ0 (glauberState Φ0 z s))) =
    uexp (fun z : Fin n → Bool =>
      poisProb (allClauses n k) m (fun l =>
        let Φ0 := subF (ofList l) (satIdx (ofList l) z)
        P Φ0 z)) := by
  sorry

end KSATSingleFlip.Connect
