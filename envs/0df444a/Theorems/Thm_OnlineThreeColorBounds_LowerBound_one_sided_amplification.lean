-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_one_sided_amplification
-- name    : OnlineThreeColorBounds.LowerBound.one_sided_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:42.780423+00:00
-- url     : https://prove2.me/theorems/0d42abf5-08a8-4714-8239-4145994fec6b
-- title:
--   Lemma 2.3 — one-sided bipartite amplification
-- statement:
--   For integers $t\ge1$ and $j\ge0$, and for every deterministic proper $t$-fold online rule $A$, there is an adaptive bipartite construction using at most $2^{j+1}-1$ vertices. In its interaction with $A$, one can designate a side $I$ of a covering bipartition such that
--   $$
--   |\operatorname{col}(I)|\ge t+j\lceil t/2\rceil.
--   $$
--   The size and bipartiteness guarantees hold on every legal response branch. The designated side can be chosen after the observed play, and is not revealed to the rule. This supplies the one-sided amplification used in Lemma 2.4, with the exact source vertex bound, including $j=0$ and $t=1$. There is no early-stop exception to the displayed conclusion.
--
--   Differences from the source:
--   - encoding: finite ordered graphs and t-element online color sets → chronological lists of earlier-neighbor and natural-color finsets; the resulting graph has carrier Fin h.length; reason: arrival indices encode every finite order, and arbitrary finite color sets can be renamed into the unbounded natural palette
--   - encoding: two sides of a bipartite graph, and col of a side → Mathlib IsBipartiteWith plus union equal to the entire vertex set, and finset unions of assigned colors; reason: isolated vertices must belong to a side; colors are counted by distinct names and two-sidedness is global across components
--   - encoding: adaptive finite graph constructions with size and post-degree bounds → well-founded response-branching trees and an AllOutcomes predicate over every exact-size proper response; reason: bounded finite plays have such a tree, with arbitrary finite-set branching; resource certificates are verified predicates rather than assumed fields
--   - encoding: s = ceiling(t/2) for cardinalities t → (t + 1) / 2 in natural arithmetic; reason: these expressions agree exactly for every natural t, including t=0 and odd t
--   - generalization: a proper t-fold coloring algorithm → properness required only on bipartite inputs and only along the rule's own runs; reason: the construction uses only bipartite graphs; every source algorithm qualifies, and no behavior on nonpromised or unreachable inputs is needed
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 2.3, printed p. 5 / PDF p. 6; proof printed p. 6 / PDF p. 7

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Construction
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Lemma 2.3, printed p. 5 / PDF p. 6. No global-target early-stop alternative. -/
theorem one_sided_amplification (t j : ℕ) (ht : 1 ≤ t)
    (A : OnlineRule) (hA : ProperOn t 2 A) :
    ∃ S : Construction, BipartiteConstruction t ((2 ^ (j + 1) - 1 : ℕ) : ℝ) S ∧
      ∃ s r : Finset (Fin (play A S []).length),
        CoveringBipartition (historyGraph (play A S [])) s r ∧
        t + j * ((t + 1) / 2) ≤ (colorsOn (play A S []) s).card := by sorry

end OnlineThreeColorBounds.LowerBound
