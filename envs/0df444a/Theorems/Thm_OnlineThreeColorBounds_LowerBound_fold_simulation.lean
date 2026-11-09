-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_fold_simulation
-- name    : OnlineThreeColorBounds.LowerBound.fold_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:35.0422+00:00
-- url     : https://prove2.me/theorems/d69af7c9-105b-4c0c-900f-7b53b8c61a37
-- title:
--   Lemma 2.5 — simulation with size and post-degree control
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $t,q,K$ be integers with $1\le t<q\le K$, and let $N,D$ be integer resource budgets with $D>0$. Suppose an adaptive three-colorable construction has size bound $N$ and post-degree bound $D$ on every legal play, and forces every proper $q$-fold online rule to use at least $K$ colors. Then there is an adaptive three-colorable construction forcing every proper $t$-fold rule to use at least $K$ colors, with integer budgets $N',D'$ satisfying both
--   $$
--   N'\le CK^2qND\,2^{Cq/t},\qquad D'\le CK^2qD\,2^{Cq/t}.
--   $$
--   Both bounds use the same positive absolute constant, independent of all parameters and the original construction. Post-degree counts only neighbors arriving later; it need not equal total degree. The output's resource bounds and offline three-colorability hold on every legal play.
--
--   This is the full simulation interface needed to retain a common target $K$ while passing between fold multiplicities. No particular simulation invariant or desired output construction is supplied as an extra hypothesis.
--
--   Differences from the source:
--   - encoding: finite ordered graphs and t-element online color sets → chronological lists of earlier-neighbor and natural-color finsets; the resulting graph has carrier Fin h.length; reason: arrival indices encode every finite order, and arbitrary finite color sets can be renamed into the unbounded natural palette
--   - encoding: adaptive finite graph constructions with size and post-degree bounds → well-founded response-branching trees and an AllOutcomes predicate over every exact-size proper response; reason: bounded finite plays have such a tree, with arbitrary finite-set branching; resource certificates are verified predicates rather than assumed fields
--   - reading: size bound N and post-degree bound D > 0, with no written scalar types → natural resource budgets N,D,N',D', with D positive; reason: the proof reserves D copies per row and R=KqD copies in Eq. (2.4); budgets count vertices and future neighbors
--   - reading: there exists a constant C > 0 after the parameter preamble → one positive real constant C quantified before every input parameter and rule; reason: the proof gives an absolute bound and §2.3 iterates it uniformly; instance-dependent constants would not express the intended result
--   - encoding: forces proper fold coloring to use K colors → Forces quantifies every deterministic rule proper on promised three-colorable inputs across all local sizes; reason: all finite proper response paths extend to such a rule using fresh colors elsewhere; fixed advice or external deterministic state can be part of the rule
--   - encoding: the two inequalities in Eq. (2.3) → real-cast natural budgets and real exponentiation with one shared C; reason: both full resource bounds are preserved, without truncating q/t or weakening either conclusion
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 2.5, Eq. (2.3), printed p. 6 / PDF p. 7; Eq. (2.4) and proof printed pp. 7–9 / PDF pp. 8–10

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Construction
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Lemma 2.5, printed p. 6 / PDF p. 7. Integer copy budgets follow the proof's R = KqD.
Both output bounds use the same uniform absolute constant. -/
theorem fold_simulation :
    ∃ C : ℝ, 0 < C ∧ ∀ t q K N D : ℕ, 1 ≤ t → t < q → q ≤ K → 0 < D →
      ∀ S : Construction, BoundedConstruction q 3 N D S → Forces q 3 K S →
        ∃ (N' D' : ℕ) (S' : Construction),
          BoundedConstruction t 3 N' D' S' ∧ Forces t 3 K S' ∧
          (N' : ℝ) ≤ C * (K : ℝ) ^ 2 * (q : ℝ) * (N : ℝ) * (D : ℝ) *
            (2 : ℝ) ^ (C * (q : ℝ) / (t : ℝ)) ∧
          (D' : ℝ) ≤ C * (K : ℝ) ^ 2 * (q : ℝ) * (D : ℝ) *
            (2 : ℝ) ^ (C * (q : ℝ) / (t : ℝ)) := by sorry

end OnlineThreeColorBounds.LowerBound
