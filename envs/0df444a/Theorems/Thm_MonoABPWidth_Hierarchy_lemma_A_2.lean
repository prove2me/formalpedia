-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_2
-- name    : MonoABPWidth.Hierarchy.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:16:57.691469+00:00
-- url     : https://prove2.me/theorems/d229dab4-cd58-40b5-ae81-793b56203751
-- title:
--   Lemma A.2 — remove irrelevant and proportional vertices (corrected: nonzero polynomial)
-- statement:
--   Let $A$ be any finite layered mABP over a finite real variable set, with nonzero output $f^{(A)}$, width $w$ and depth $d$. There is an mABP $B$ with
--   $$
--   f^{(B)}=f^{(A)},\qquad \operatorname{width}(B)\le w,\qquad \operatorname{depth}(B)\le d,
--   $$
--   such that every vertex of $B$ has nonzero prefix and suffix and distinct vertices in a layer have pairwise nonproportional prefixes and pairwise nonproportional suffixes. This supplies properties 1 and 2 of Definition A.1 without changing the computed polynomial.
--
--   Differences from the source:
--   - correction: arbitrary output, including zero → nonzero output; reason: a depth-one width-one zero-labelled edge computes zero, and any equivalent program has zero prefix at its sink, violating property 1
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma A.2, p. 27, PDF 28

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity

namespace MonoABPWidth.Hierarchy

/-- Lemma A.2, p.27 / PDF28, corrected by requiring nonzero output. A single zero edge
computes zero, but relevance forces a nonzero prefix at the sink. -/
theorem lemma_A_2 {σ : Type} [Fintype σ] (A : MABP σ) (hzero : A.output ≠ 0) :
    ∃ B : MABP σ, B.width ≤ A.width ∧ B.depth ≤ A.depth ∧
      B.Relevant ∧ B.Nonproportional ∧ B.output = A.output := by sorry

end MonoABPWidth.Hierarchy
