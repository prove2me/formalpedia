-- Prove2me | Theorems.Thm_OPG37364_immune_high_girth_graphs
-- name    : OPG37364.immune_high_girth_graphs
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T04:51:32.465776+00:00
-- url     : https://prove2.me/theorems/be682b4a-46e3-411c-beb5-1970bca8908c
-- title:
--   Lemma 5: immune 14-regular bipartite graphs of arbitrary girth
-- statement:
--   For every integer $g\ge3$, there exists a finite connected bipartite graph $G$ with at least two vertices such that
--
--   $$
--   G\text{ is $14$-regular},\qquad
--   \operatorname{girth}(G)\ge g,\qquad
--   G\text{ has no matching cut},
--   $$
--
--   and $G$ contains a perfect matching. The graph may depend on $g$. This is the structural existence theorem stated as Lemma 5 in the cited paper.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199-1221, https://doi.org/10.1007/s00453-025-01318-8, Lemma 5

import Definitions.Def_opg37364_matching_cuts

namespace OPG37364

/-- Feghali--Lucke--Paulusma--Ries, Lemma 5: immune 14-regular bipartite
graphs with arbitrarily large prescribed girth and a perfect matching. -/
theorem immune_high_girth_graphs :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsImmuneHighGirthPackage G g := by sorry

end OPG37364
