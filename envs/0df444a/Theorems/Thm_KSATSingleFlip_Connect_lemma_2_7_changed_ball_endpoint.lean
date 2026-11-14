-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_changed_ball_endpoint
-- name    : KSATSingleFlip.Connect.lemma_2_7_changed_ball_endpoint
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:38.072414+00:00
-- url     : https://prove2.me/theorems/54d2ce3d-576f-417c-bfbd-cb92228e03e8
-- title:
--   Changed trimmed balls contain an inserted-clause endpoint
-- statement:
--   If appending a clause changes a trimmed locally tree-structured factor ball, then some variable of the appended clause lies in that root’s old or new trimmed ball. Clause occurrence labels of existing clauses are kept fixed. This is the local containment step in the proof of Lemma 2.7; it includes changes caused by the degree cutoff as well as changes to the ball itself.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 2.7, printed p. 13 (PDF p. 15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- A changed trimmed ball contains an endpoint of the inserted clause
in the old or the new locally tree-structured ball. -/
theorem lemma_2_7_changed_ball_endpoint {n : ℕ} (Φ : GFormula (Fin n))
    (C : GClause (Fin n)) (r D : ℕ) :
    ∀ v : Fin n, trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D →
      ∃ u ∈ vbl C,
        (LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r) ∨
        (LocallyTree (Φ ++ [C]) v r D ∧ u ∈ ballVars (Φ ++ [C]) v r) := by
  sorry

end KSATSingleFlip.Connect
