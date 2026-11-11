-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_theorem_4
-- name    : LowDiameterNashWilliams.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:40.802344+00:00
-- url     : https://prove2.me/theorems/3a19578d-543c-4cee-b707-832553fd5883
-- title:
--   Theorem 4 — Shortening theorem
-- statement:
--   There are absolute positive constants $C,C_T$, a threshold $K$, and a single randomized finite program. Let $k\ge K$, let a simple $n$-vertex graph, $n\ge2$, have an exact tree partition, and partition its indices into receiving $I$ and supplying $J$. Suppose every vertex outside $S$ is a leaf in at least $k/128$ supplying trees. There are a new exact partition and $S'\supseteq S$ satisfying
--
--   $$\operatorname{diam}(T'_i)\le C(|S|+n/k),\qquad |\operatorname{int}(T'_i)|\le C(|S|+(n/k)\log k)\quad(i\in I),$$
--   $$\operatorname{diam}(T'_j)\le\operatorname{diam}(T_j)+2,\qquad |\operatorname{int}(T'_j)|\le|\operatorname{int}(T_j)|+C(n/k)\log k\quad(j\in J),$$
--   $$|S'|\le C(|S|+n/k),\qquad |\{i\in I:v\in\operatorname{int}(T'_i)\}|<k/8\quad(v\notin S').$$
--
--   Given the original partition and the indicated classes and exceptional set, the program returns these objects correctly whenever it halts, terminates almost surely, and has expected charged time at most $C_Tkn^3\log k$. This retains the supplying-tree increases and the strict exceptional-set conclusion needed for a second shortening call.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
--   - encoding: deterministic or randomized algorithm with the stated operation-time bound → one finite program and word coefficient before the inputs, charged published word-RAM execution, literal output masks, tail-sum extended expected cost or worst-case deterministic cost; reason: standard O(log n)-bit word operations from Section 4.4; no free algorithm calls, cost annotations or ignored retries; Lemma 4.2 additionally allows log d bits to read d
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 4, p. 11 (PDF p. 12)

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

theorem theorem_4 :
  ∃ C C_T : ℝ, 0 < C ∧ 0 < C_T ∧ ∃ K c : ℕ, 2 ≤ K ∧ 0 < c ∧ ∃ P : Program,
  ∀ n m k : ℕ, 2 ≤ n → K ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (I J : Finset (Fin k)) (S : Finset (Fin n)),
  Simple ends → TreePartition ends T → Disjoint I J → I ∪ J = Finset.univ →
  (∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends T J v) →
  (∃ (U : Trees k m) (S' : Finset (Fin n)), Shortened ends C T U I J S S') ∧
  Runs P (wordSize c n 0)
    (graphWords ends ++ [k] ++ treeWords T ++ setWords I ++ setWords J ++ setWords S)
    (fun mem => ∃ (U : Trees k m) (S' : Finset (Fin n)),
      Outputs mem (treeWords U ++ setWords S') ∧ Shortened ends C T U I J S S')
    (C_T * k * (n : ℝ) ^ 3 * Real.log k) := by sorry

end LowDiameterNashWilliams.Main
