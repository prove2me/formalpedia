-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_padding_distance_loss
-- name    : GraphIsoTesting.FixedGraph.padding_distance_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:37:13.040679+00:00
-- url     : https://prove2.me/theorems/3380e094-692f-4b56-b78a-be511a17ef44
-- title:
--   Remark 3.7 — Distance loss from isolated padding (implementation obligation)
-- statement:
--   Let $G,H$ be two simple graphs on the same finite core vertex set, both of maximum degree at most $d$. For any natural $r$, adding $r$ isolated vertices to both graphs satisfies
--
--   $$\operatorname{dist}_{\rm iso}(G\sqcup I_r,H\sqcup I_r)
--   \ge\operatorname{dist}_{\rm iso}(G,H)-4dr.$$
--
--   The Lean inequality uses the equivalent additive form to avoid truncated natural subtraction. Both distances minimize over all vertex bijections, including bijections mixing core and added vertices.
--
--   This is the unnumbered quantitative bridge implementing Remark 3.7's bounded-size augmentation. It is included as a theorem obligation and is not an assumed condition of the graph-testing result. The intended all-size realization uses $r=N\bmod13\le12$ isolated vertices; the bound absorbs their constant contribution without increasing degree 13.
--
--   Differences from the source:
--   - generalization: bounded-size augmentation of the constructed graphs in Remark 3.7 → the quantitative isolated-padding inequality for all finite core graphs and every natural r; reason: the finite-set bound also holds beyond the application r ≤ 12; specializing gives the required all-size bridge
--   - encoding: a bounded-size augmentation has negligible effect on the analysis → isolated padding with the explicit bound dist(core) ≤ dist(padded) + 4dr for all finite cores and r; reason: this makes the chosen implementation obligation explicit; r ≤ 12 in the application, preserving the source all-size conclusion
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 14, Remark 3.7, quantitative isolated-padding implementation (no numbered lemma in source)

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_Padding

namespace GraphIsoTesting.FixedGraph

theorem padding_distance_loss {V : Type} [Fintype V]
    (G H : SimpleGraph V) (d r : ℕ) (hG : DegreeBound G d) (hH : DegreeBound H d) :
    isoDistance G H ≤ isoDistance (isolatedPadding G r) (isolatedPadding H r) + 4 * d * r := by sorry

end GraphIsoTesting.FixedGraph
