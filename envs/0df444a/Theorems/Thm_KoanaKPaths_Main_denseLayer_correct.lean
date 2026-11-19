-- Prove2me | Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
-- name    : KoanaKPaths.Main.denseLayer_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:52.259014+00:00
-- url     : https://prove2.me/theorems/7df5a118-3cee-428c-a544-31c6f631087a
-- title:
--   Dense coefficient arrays realize the exterior graph-sketch recurrence
-- statement:
--   Let a directed graph on $n$ vertices be represented by an arc list, let $\sigma$ assign $k$ sign coordinates to each vertex, and let $R$ be the sketch signs of width $\ell$. For every layer $p\ge0$, vertex $v<n$ and sketch state $a<\ell$, the concrete length-$2^k$ array evaluator agrees with the exterior-coordinate recurrence:
--   $$
--   \operatorname{denseLayer}(p,v,a)=\operatorname{coefficientList}\bigl(\operatorname{graphLayer}(p,v,a)\bigr).
--   $$
--   Both sides use the same arc membership and shared signs. The theorem requires neither graph simplicity nor positivity of $k$ and covers the zero layers specified outside the recurrence's active range. It is the representation-correctness bridge from a finite integer-array implementation to the algebraic sketch used in the counting proof.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/DenseGraph.lean, line 39; source snapshot SHA-256 c8b8437b8f07b89cf54325da7b780621310da6eeefe35146c9436da8685d70f3.

import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Main.denseLayer_correct :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ) (p : Nat) (v : Fin n) (a : Fin ℓ),
  @Eq.{1} (List.{0} Int) (@KoanaKPaths.Main.denseLayer n k ℓ arcs σ R p v a)
    (@KoanaKPaths.ExteriorCoordinates.coefficientList k (@KoanaKPaths.Main.graphLayer n k ℓ arcs σ R p v a)) := by sorry
