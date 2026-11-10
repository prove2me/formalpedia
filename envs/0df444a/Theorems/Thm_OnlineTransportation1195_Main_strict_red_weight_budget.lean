-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_strict_red_weight_budget
-- name    : OnlineTransportation1195.Main.strict_red_weight_budget
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:21.651687+00:00
-- url     : https://prove2.me/theorems/38e478ab-1974-47a1-ad63-3636424344d0
-- title:
--   Lemma 3.6 — strict red-weight budget
-- statement:
--   Let $T$ have positive edge weights, positive root-monotone deadlines with $\sum_e w_e/d_e=1$, and fix any root-based DFS. If the deadlines are not all equal, then
--
--   $$\exists t>0,\qquad R(t)<F(t).$$
--
--   This is the full strict budget statement under the standing assumptions of Section 3. Both $R$ and $F$ are computed from the same input and the chosen DFS.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - encoding: any fixed root-based depth-first walk and its first-edge downward costs → a vertex list traversing each edge once in each direction; computed x, red edges and root patch; reason: on a tree these are exactly the depth-first tours; the list is fixed before time budgets are quantified
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Lemma 3.6, PDF / printed p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_RedPatches

namespace OnlineTransportation1195.Main

theorem strict_red_weight_budget {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (hne : T.Unequal d) :
    ∃ t : ℝ, 0 < t ∧ T.R d L t < T.F d t := by sorry

end OnlineTransportation1195.Main
