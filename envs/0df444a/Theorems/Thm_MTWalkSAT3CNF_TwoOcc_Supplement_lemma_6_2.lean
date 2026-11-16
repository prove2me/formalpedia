-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_lemma_6_2
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:03:32.862593+00:00
-- url     : https://prove2.me/theorems/9b99493d-0705-49b4-86bb-35fda825f80c
-- title:
--   Lemma 6.2 — An explicitly constructible growing family of 102-regular graphs with all nonleading eigenvalues below 21 in absolute value
-- statement:
--   There is an algorithm outputting a finite adjacency matrix for each index $j\ge1$, defining simple connected 102-regular graphs $G_j$ whose vertex counts $N_j$ tend to infinity and whose real adjacency eigenvalues, sorted decreasingly with multiplicity, satisfy
--
--   $$\lambda_1(G_j)=102,\qquad |\lambda_i(G_j)|<21\quad(2\le i\le N_j).$$
--
--   Explicit constructibility is retained as computability of the matrix-code output function; no running-time bound on the construction is imposed. Negative eigenvalues are included in the absolute-value condition. This supplies the graph family used by the separation theorem.
--
--   Differences from the source:
--   - encoding: an explicitly constructible graph family indexed by j≥1 → a computable function on ℕ returning vertex counts and adjacency-bit codes, with sorted real adjacency eigenvalues; reason: j in Lean corresponds to j+1 in the source; decoding finite codes gives the actual matrices, and the statement keeps all spectral and growth conditions
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Lemma 6.2, p. 35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem lemma_6_2 :
    ∃ f : ℕ → ℕ × ℕ, ExplicitExpanderFamily f := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
