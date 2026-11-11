-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_17
-- name    : MatchIndiff.PublicSM.lemma_D_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:51.504357+00:00
-- url     : https://prove2.me/theorems/4cc55ca0-e623-46d7-895b-1626a0b94d38
-- title:
--   Lemma D.17 — an accepted mask and comparison tape replay the true execution; m_Q + 2|E| bits suffice
-- statement:
--   Fix public priorities $Q$, a deterministic public procedure that makes comparison requests, and the actual student rows $P$; let $E$ be the set of mutually acceptable pairs. If all students accept the row bits and a comparison tape, then the published mask is exactly $E$ and the public execution is the execution on the actual mutual pairs and actual student comparisons: every recorded answer is the named student's true answer and the procedure stops exactly at the end of the tape. Consequently, if the procedure makes at most $|E|$ comparison requests on the actual data, it has a student-local transcript certificate of at most
--   $$m_Q+2|E|$$
--   bits (one bit per public pair position and two per request), apart from its public initial data.
--
--   Algorithms 15 and 16, at any fixed choice rules, are such procedures; this is how Theorem D.8 records only answers, not request identities.
--
--   Differences from the source:
--   - reading: its public execution is the execution on the actual mutual pairs and actual student comparisons → the mask decodes to the actual mutual graph trueE, and replaying the tape on it yields an answer list that IsTrueRun (every answer true for its request, the procedure stops after the last one); reason: the formal content of executing on actual data
--   - reading: a procedure (with public initial data) → any Procedure: a function of the mutual-pair graph and the previous answers to the next request or stop; public initial data are part of the function; reason: covers Algorithms 15 and 16 at every fixed choice rule, as the lemma intends
--   - encoding: row bits in fixed school and student identifier order, two-bit answers with the fourth code forbidden, certificate length in bits → board : List Bool = mask in pubPairs order followed by the tape; codes 00/01/10, 11 rejected; length board.length; reason: Lean convention
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 99, Lemma D.17

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Tape

namespace MatchIndiff.PublicSM

/-- Lemma D.17 (p. 99): if all students accept the row bits and a comparison tape, the mask is the
actual mutual-pair graph and the public execution is the execution on the actual mutual pairs and
actual student comparisons; a procedure making at most `|E|` comparison requests has a
student-local transcript certificate of at most `m_Q + 2|E|` bits. -/
theorem lemma_D_17 {n m : ℕ} (Q : Fin m → Fin n → ℕ) (P : Fin n → Fin m → ℕ)
    (hQ : ∀ h, IsRow (Q h)) (hP : ∀ i, IsRow (P i)) (proc : Procedure n m) :
    (∀ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) →
      maskE Q (board.take (pubPairs Q).length) = trueE Q P ∧
        ∃ ans, replay (proc (trueE Q P)) [] (board.drop (pubPairs Q).length) = some ans ∧
          IsTrueRun proc (trueE Q P) P ans) ∧
    (∀ ans : List Ans, IsTrueRun proc (trueE Q P) P ans →
      ans.length ≤ (Finset.univ.filter (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card →
      ∃ board : List Bool, (∀ d, tapeCheck Q proc d (P d) board = true) ∧
        board.length ≤ mQ Q + 2 * (Finset.univ.filter
          (fun x : Fin n × Fin m => trueE Q P x.1 x.2 = true)).card) := by sorry

end MatchIndiff.PublicSM
