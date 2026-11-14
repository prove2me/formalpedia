-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_changed_balls
-- name    : KSATSingleFlip.Connect.lemma_2_7_changed_balls
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:10.02822+00:00
-- url     : https://prove2.me/theorems/80d63b5b-0712-45b6-9eb7-5a347af653f8
-- title:
--   One clause changes few trimmed factor balls
-- statement:
--   Under the hypotheses of Lemma 2.7, appending a clause with at most $k$ variables changes at most $2kM_{r,D}$ locally tree-structured trimmed balls, where $M_{r,D}=\sum_{h=0}^{r+1}(kD)^h$. The representation retains original clause occurrence labels, variable identities, and signed clauses. This is the changed-ball cardinality component of the lemma.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.7 and (2.1), printed pp. 12–13 (PDF pp. 14–15), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_TrimmedBall

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- The changed-ball cardinality statement in Lemma 2.7. -/
theorem lemma_2_7_changed_balls {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h := by
  sorry

end KSATSingleFlip.Connect
