-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_two_sided_or_target
-- name    : OnlineThreeColorBounds.LowerBound.two_sided_or_target
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:33.237209+00:00
-- url     : https://prove2.me/theorems/2b1e9eba-1392-49d7-99f8-65965e0b3501
-- title:
--   Lemma 2.4 — two-sided colors or the global target
-- statement:
--   There is an absolute constant $C>0$ such that, for all integers $K\ge2$ and $1\le t\le q\le K$, every deterministic proper $t$-fold online rule $A$ admits an adaptive bipartite construction with at most
--   $$
--   CK\,2^{Cq/t}
--   $$
--   vertices. Its completed interaction with $A$ satisfies at least one alternative:
--   $$
--   C_A\ge K\qquad\text{or}\qquad
--   |\operatorname{col}(L)\cap\operatorname{col}(R)|\ge q
--   $$
--   for some covering bipartition $(L,R)$ of the whole constructed graph. Resource and bipartiteness guarantees apply to all legal plays; the final sides may be reoriented after the observed play. A two-sided color may occur in different connected components on the two sides.
--
--   This alternative supplies the bipartite building blocks for fold simulation. The same absolute constant is independent of $K,t,q$ and $A$, and there is no restriction on the magnitude of the online color names.
--
--   Differences from the source:
--   - encoding: finite ordered graphs and t-element online color sets → chronological lists of earlier-neighbor and natural-color finsets; the resulting graph has carrier Fin h.length; reason: arrival indices encode every finite order, and arbitrary finite color sets can be renamed into the unbounded natural palette
--   - encoding: two sides of a bipartite graph, and col of a side → Mathlib IsBipartiteWith plus union equal to the entire vertex set, and finset unions of assigned colors; reason: isolated vertices must belong to a side; colors are counted by distinct names and two-sidedness is global across components
--   - encoding: adaptive finite graph constructions with size and post-degree bounds → well-founded response-branching trees and an AllOutcomes predicate over every exact-size proper response; reason: bounded finite plays have such a tree, with arbitrary finite-set branching; resource certificates are verified predicates rather than assumed fields
--   - generalization: a proper t-fold coloring algorithm → properness required only on bipartite inputs and only along the rule's own runs; reason: the construction uses only bipartite graphs; every source algorithm qualifies, and no behavior on nonpromised or unreachable inputs is needed
--   - reading: there exists a constant C > 0 after the parameter preamble → one positive real constant C quantified before every input parameter and rule; reason: the proof gives an absolute bound and §2.3 iterates it uniformly; instance-dependent constants would not express the intended result
--   - encoding: the bound CK 2^(Cq/t) → real arithmetic and real exponentiation, with integer t at least one; reason: the source ratio is not natural-number division and cannot have a zero denominator
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 2.4, printed p. 6 / PDF p. 7; absolute-constant use §2.3, printed p. 9 / PDF p. 10

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Construction
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Lemma 2.4, printed p. 6 / PDF p. 7. The constant precedes all input parameters. -/
theorem two_sided_or_target :
    ∃ C : ℝ, 0 < C ∧ ∀ K t q : ℕ, 2 ≤ K → 1 ≤ t → t ≤ q → q ≤ K →
      ∀ A : OnlineRule, ProperOn t 2 A →
        ∃ S : Construction,
          BipartiteConstruction t (C * (K : ℝ) * (2 : ℝ) ^ (C * (q : ℝ) / (t : ℝ))) S ∧
          (K ≤ colorCount (play A S []) ∨
            ∃ s r : Finset (Fin (play A S []).length),
              CoveringBipartition (historyGraph (play A S [])) s r ∧
              q ≤ (twoSidedColors (play A S []) s r).card) := by sorry

end OnlineThreeColorBounds.LowerBound
