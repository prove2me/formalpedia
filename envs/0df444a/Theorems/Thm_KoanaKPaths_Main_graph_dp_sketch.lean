-- Prove2me | Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
-- name    : KoanaKPaths.Main.graph_dp_sketch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:45:43.11922+00:00
-- url     : https://prove2.me/theorems/f9be250c-5843-4fb9-81d6-dec8aca05e10
-- title:
--   The walk dynamic program computes the recursive sketch norm
-- statement:
--   Let $k\ge1$, and let a directed graph on $n$ vertices be given by its arc list, interpreted as an arc set. Fix arbitrary sign labels and sketch matrices of width $\ell$. Let $c$ be the zero-one coefficient tensor of the graph's $k$-vertex walks, and let $S_k$ be its recursively contracted determinant-weighted sketch. The exterior dynamic program above satisfies
--
--   $$
--   \sum_{a=1}^{\ell}\left([e_{[k]}]\sum_v F_{k,v,a}\right)^2=\|S_k\|_F^2.
--   $$
--
--   Thus its terminal full-subset coefficients determine exactly the numerator of the estimator analyzed in Lemma 6. The equality includes empty graphs and zero-width sketches. This is an algebraic correctness theorem; it does not itself assert a machine-time bound.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 8 / PDF p. 9, Section 3.2, equation (3.2) and the output-coefficient identity; printed p. 9 / PDF p. 10, Section 4.1, directed-walk recurrence. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_GraphDP
open scoped BigOperators

theorem KoanaKPaths.Main.graph_dp_sketch {n k ℓ : ℕ} (hk : 1 ≤ k) (arcs : List (Fin n × Fin n))
    (σ : KoanaKPaths.Main.Labels n k) (R : KoanaKPaths.Main.SketchSigns n k ℓ) :
    (∑ a : Fin ℓ, (KoanaKPaths.Main.graphOutput arcs σ R a Finset.univ)^2) =
      KoanaKPaths.Main.sketchFrobSq (KoanaKPaths.Main.walkTensor n arcs k) σ R k := by sorry
