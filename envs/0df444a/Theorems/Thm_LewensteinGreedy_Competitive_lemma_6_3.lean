-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_lemma_6_3
-- name    : LewensteinGreedy.Competitive.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:31:47.140028+00:00
-- url     : https://prove2.me/theorems/46b6f132-88d0-4119-b95c-69fc3c699ad3
-- title:
--   Lemma 6.3 — monotone column projection preserves arboreal satisfaction
-- statement:
--   If $P$ is a finite arboreally satisfied point set and $\pi$ is a nondecreasing map on its ordered key columns, then $\pi(P)=\{(\pi(x),t):(x,t)\in P\}$ is arboreally satisfied and $|\pi(P)|\le|P|$.
--
--   Differences from the source:
--   - generalization: point sets of key/time points (integer coordinates) and a nondecreasing map of key columns → finite P ⊆ ℝ × ℝ and π : ℝ → ℝ monotone on the set of key columns of P; reason: the proof uses only the order of coordinates; integer point sets and column maps embed in ℝ, so the source's statement is the special case
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Lemma 6.3, printed p. 40 / PDF 41

import Mathlib
import Definitions.Def_LewensteinGreedy_Competitive_Geometry

namespace LewensteinGreedy.Competitive

/-- Lemma 6.3 (monotone column projection), printed p.40 / PDF 41: the image of a finite
arboreally satisfied point set under a nondecreasing map of its key columns is arboreally
satisfied and has at most as many points. -/
theorem lemma_6_3 (P : Finset (ℝ × ℝ)) (π : ℝ → ℝ) (hP : ArboreallySatisfied P)
    (hπ : MonotoneOn π (P.image Prod.fst : Set ℝ)) :
    ArboreallySatisfied (projectColumns π P) ∧ (projectColumns π P).card ≤ P.card := by sorry

end LewensteinGreedy.Competitive
