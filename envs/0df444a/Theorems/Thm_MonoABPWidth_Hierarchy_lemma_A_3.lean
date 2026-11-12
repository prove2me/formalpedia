-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_3
-- name    : MonoABPWidth.Hierarchy.lemma_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T08:17:05.416994+00:00
-- url     : https://prove2.me/theorems/2f7d577f-8486-4d4b-b578-57a49771261f
-- title:
--   Lemma A.3 — homogeneity of prefixes, suffixes, and edges
-- statement:
--   Let $A$ be a finite layered mABP over a finite real variable set, satisfying relevance (property 1 of Definition A.1). If its computed polynomial is homogeneous, then
--   $$
--   \text{every }f_{s\to v}\text{ and }f_{v\to t}\text{ is homogeneous, and every edge label is homogeneous of degree at most }1.
--   $$
--   The degrees of different intermediate polynomials need not agree. Zero labels are included and are homogeneous of degree zero. This records the full homogeneity conclusion needed to analyze simplified programs.
--
--   Differences from the source:
--   - encoding: one-based matrix and vertex indices; width w → zero-based Fin indices; largest layer cardinality at most w; reason: finite relabelling preserves every program; the proof uses bounded width (pp.7,9)
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), Lemma A.3, p. 27, PDF 28

import Definitions.Def_MonoABPWidth_Hierarchy_simplicity

namespace MonoABPWidth.Hierarchy

/-- Lemma A.3, p.27 / PDF28: the whole intermediate-homogeneity conclusion,
including every edge and its degree bound. -/
theorem lemma_A_3 {σ : Type} [Fintype σ] (A : MABP σ)
    (hrel : A.Relevant) (hhom : Homogeneous A.output) :
    (∀ (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)),
      Homogeneous (A.prefix i v) ∧ Homogeneous (A.suffix i v)) ∧
    (∀ (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc))
      (v : Fin (A.layerSize e.succ)),
      ∃ q : ℕ, q ≤ 1 ∧ (A.label e u v).poly.IsHomogeneous q) := by sorry

end MonoABPWidth.Hierarchy
