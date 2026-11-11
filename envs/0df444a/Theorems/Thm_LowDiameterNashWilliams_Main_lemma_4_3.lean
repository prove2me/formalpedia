-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_3
-- name    : LowDiameterNashWilliams.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:56.892411+00:00
-- url     : https://prove2.me/theorems/ac4b4239-a952-4afd-9ef4-1fdeb3e6ead1
-- title:
--   Lemma 4.3 — Restoring the supplying trees
-- statement:
--   There are an absolute $C>0$ and an absolute threshold $K$ with the following property. Let $k\ge K$ and let a simple $n$-vertex graph, $n\ge2$, have an exact tree partition $T_1,\ldots,T_k$. Partition the indices into arbitrary receiving and supplying classes $I,J$. Suppose every vertex outside $S$ is a leaf in at least $k/128$ supplying trees. Put $r=\lfloor k/8192\rfloor$.
--
--   There are $H\supseteq S$ and pairwise disjoint owner reserves from supplying edges such that
--
--   $$|H\setminus S|\le n/k,\qquad |R_v|=r\ (v\notin H),\qquad R_v=\varnothing\ (v\in H).$$
--
--   Fix these reserves before any exchange. For every exact repartition of the available receiving-tree and reserve edges into new receiving spanning trees and incident owner reserves of unchanged cardinality, the complementary host edges admit a supplying-tree partition with
--
--   $$\operatorname{diam}(T'_j)\le\operatorname{diam}(T_j)+2,\qquad
--   |\operatorname{int}(T'_j)|\le|\operatorname{int}(T_j)|+C(n/k)\log k\quad(j\in J).$$
--
--   Comparison is with the original supplying trees. The single choice of reserves works for every permitted later repartition, providing the universal restoration guarantee.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 4.3, p. 14 (PDF p. 15)

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

theorem lemma_4_3 :
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ n m k : ℕ, 2 ≤ n → K ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (I J : Finset (Fin k)) (S : Finset (Fin n)),
  Simple ends → TreePartition ends T → Disjoint I J → I ∪ J = Finset.univ →
  (∀ v, v ∉ S → (k : ℝ) / 128 ≤ leafCount ends T J v) →
  ∃ (H : Finset (Fin n)) (R : Fin n → Edges m),
    S ⊆ H ∧ ((H \ S).card : ℝ) ≤ (n : ℝ) / k ∧ OwnerReserves ends R ∧
    (∀ v, R v ⊆ J.biUnion T) ∧
    (∀ v, (v ∉ H → (R v).card = k / 8192) ∧ (v ∈ H → R v = ∅)) ∧
    ∀ (U : Trees k m) (R' : Fin n → Edges m),
      ExchangePartition ends I U R' (I.biUnion T ∪ Finset.univ.biUnion R) →
      (∀ v, (R' v).card = (R v).card) →
      ∃ V : Trees k m, TreePartition ends V ∧ (∀ i ∈ I, V i = U i) ∧
        ∀ j ∈ J, diameter ends (V j) ≤ diameter ends (T j) + 2 ∧
          ((internal ends (V j)).card : ℝ) ≤ (internal ends (T j)).card +
            C * ((n : ℝ) / k * Real.log k) := by sorry

end LowDiameterNashWilliams.Main
