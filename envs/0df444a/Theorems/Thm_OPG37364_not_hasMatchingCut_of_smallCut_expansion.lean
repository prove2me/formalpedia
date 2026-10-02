-- Prove2me | Theorems.Thm_OPG37364_not_hasMatchingCut_of_smallCut_expansion
-- name    : OPG37364.not_hasMatchingCut_of_smallCut_expansion
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T08:52:53.906974+00:00
-- url     : https://prove2.me/theorems/e1df0c30-1fb5-4d22-b53d-b6357e88d447
-- title:
--   Strict expansion of small cuts implies immunity
-- statement:
--   Let $G$ be a finite simple graph on $V$. Suppose that every nonempty proper shore $S\subset V$ satisfying $|S|\le |V\setminus S|$ has strictly more crossing edges than vertices:
--
--   $$|S|<|\operatorname{cutPairs}(G,S)|.$$
--
--   Then $G$ has no matching cut, where a matching cut is a bipartition into nonempty shores with at most one crossing neighbor at each vertex.
--
--   This is the elementary expansion-to-immunity implication used in Observation 2 and Lemma 5 of the cited paper. No regularity, bipartiteness, connectedness, girth, or spectral assumptions are required.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199--1221, https://link.springer.com/article/10.1007/s00453-025-01318-8, Observation 2 (matching-cut case) and its use in the proof of Lemma 5; crossing-pair cardinality formulation of that elementary implication.

import Definitions.Def_opg37364_cut_pairs

set_option autoImplicit false

namespace OPG37364

universe u

theorem not_hasMatchingCut_of_smallCut_expansion {V : Type u} {G : SimpleGraph V} [Finite V]
    (hExpansion : ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty →
      S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard) :
    ¬ HasMatchingCut G := by sorry

end OPG37364
