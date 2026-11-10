-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_normalized_downward_deadlines
-- name    : OnlineTransportation1195.Main.normalized_downward_deadlines
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:25.14707+00:00
-- url     : https://prove2.me/theorems/502d09fc-46ea-4524-8d83-b8f11b22a4da
-- title:
--   Theorem 3.1 — normalized downward-cost deadlines
-- statement:
--   Let $T$ be any finite rooted tree with positive real edge weights $w_e$ and positive deadlines $d_e$ that are nondecreasing along root paths. If $\sum_e w_e/d_e=1$, there is an actual walk $L$ starting at the root, visiting every edge, such that
--
--   $$\operatorname{downwardCost}(L\text{ through the first crossing of }e)\le d_e\quad(e\in E).$$
--
--   Movement away from the root is charged and upward movement is free. Weights themselves need not be monotone. Equal deadlines are included. This is the complete normalized theorem; it has no additional computation clause in its printed statement.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - encoding: a finite rooted walk and its downward cost through the first traversal → a root-first adjacent-vertex list, with a witnessed first crossing and an inclusive downward prefix sum; reason: the list records exactly the source walk; downward moves pay their positive weight and upward moves pay zero
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Theorem 3.1, PDF / printed p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_TreeWalk

namespace OnlineTransportation1195.Main

theorem normalized_downward_deadlines {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (hD : T.Normalized d) :
    ∃ L : List (Fin n), T.DownDeadlines L d := by sorry

end OnlineTransportation1195.Main
