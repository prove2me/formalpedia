-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_theorem_2
-- name    : LowDiameterNashWilliams.Main.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:49.552641+00:00
-- url     : https://prove2.me/theorems/9e3a7a6d-133d-462c-8547-2cee869dd5da
-- title:
--   Theorem 2 — Leaf supply
-- statement:
--   Let a simple $n$-vertex graph, $n\ge2$, have its edges partitionable into $k\ge1$ spanning trees. There is an absolute $C>0$, an exact new partition $T_1,\ldots,T_k$, and $S\subseteq V$ such that
--
--   $$|S|\le Cn/k,\qquad
--   \bigl|\{i\le\lceil k/2\rceil:v\text{ is a leaf of }T_i\}\bigr|\ge k/128\quad(v\notin S).$$
--
--   The initial partition is an existence hypothesis. This is the exact numbered structural theorem; its implementation in Section 3.5 supplies context for the later algorithmic conclusions.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 2, p. 5 (PDF p. 6)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main

theorem theorem_2 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ ends : Fin m → Sym2 (Fin n), Simple ends →
  (∃ T : Trees k m, TreePartition ends T) →
  ∃ (U : Trees k m) (S : Finset (Fin n)), TreePartition ends U ∧
    (S.card : ℝ) ≤ C * ((n : ℝ) / k) ∧
    ∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends U (firstHalf k) v := by sorry

end LowDiameterNashWilliams.Main
