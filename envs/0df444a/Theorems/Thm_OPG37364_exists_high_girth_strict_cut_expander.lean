-- Prove2me | Theorems.Thm_OPG37364_exists_high_girth_strict_cut_expander
-- name    : OPG37364.exists_high_girth_strict_cut_expander
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T08:58:05.853837+00:00
-- url     : https://prove2.me/theorems/fe4b7673-1145-453e-8506-2b7f22c532da
-- title:
--   High-girth 14-regular bipartite graphs with strict cut expansion
-- statement:
--   For every integer $g\ge3$, there exist an integer $n\ge2$ and a connected bipartite simple graph $G$ on $n$ vertices such that every vertex has degree fourteen, every simple cycle has length at least $g$, and every nonempty proper shore $S$ with $|S|\le|V(G)\setminus S|$ satisfies
--
--   $$|\operatorname{cutPairs}(G,S)|>|S|.$$
--
--   This isolates the still-hard graph-existence input from the LPS/expander route in the proof of Lemma 5. It asks for the construction's strict expansion property; it does not include immunity or a perfect matching in its conclusion. Those are separate general consequences. No construction or spectral theorem is postulated by a definition.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199--1221, https://link.springer.com/article/10.1007/s00453-025-01318-8, proof of Lemma 5: the LPS graph family has arbitrarily large girth and h(G) >= 7 - sqrt(13) > 1, before applying Observation 2 and Hall. This node records that intermediate existence assertion, not a completed formalization of LPS.

import Definitions.Def_opg37364_cut_pairs

set_option autoImplicit false

namespace OPG37364

theorem exists_high_girth_strict_cut_expander :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (∀ S : Set (Fin n), S.Nonempty → Sᶜ.Nonempty →
          S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard) := by sorry

end OPG37364
