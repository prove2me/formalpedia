-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_1
-- name    : LowDiameterNashWilliams.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:46.459782+00:00
-- url     : https://prove2.me/theorems/2ad971f5-171b-4a79-9a1a-2c6a54fc9beb
-- title:
--   Lemma 4.1 — Shortening one receiving tree
-- statement:
--   Let $T$ be a spanning tree of a simple graph on $n\ge2$ vertices. For each vertex $v$ let $R_v$ be a reserve of edges incident with $v$, and assume the tree and all reserves are pairwise disjoint. Let $A,B\subseteq V$, $d\ge2$, and suppose every $v\notin B$ owns at least $d$ reserved edges to $A$. The available edges can be exactly repartitioned into a spanning tree $T'$ and incident owner reserves $R'_v$ with $|R'_v|=|R_v|$, such that
--
--   $$\operatorname{diam}(T')\le C(|B|+|A|/d),\qquad
--   |\operatorname{int}(T')\setminus(A\cup B)|\le2(|B|+|A|/d).$$
--
--   Only the diameter has an implicit absolute constant; the internal-vertex estimate retains its exact factor two. The preserved owner cardinalities permit later restoration.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 4.1, p. 12 (PDF p. 13)

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

theorem lemma_4_1 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m d : ℕ, 2 ≤ n → 2 ≤ d →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (R : Fin n → Edges m)
    (A B : Finset (Fin n)), Simple ends → IsSpanningTree ends T →
  OwnerReserves ends R → (∀ v, Disjoint T (R v)) →
  (∀ v, v ∉ B → d ≤ reserveNeighbors ends R v A) →
  ∃ (Q : Edges m) (R' : Fin n → Edges m), IsSpanningTree ends Q ∧
    OwnerReserves ends R' ∧ (∀ v, Disjoint Q (R' v)) ∧
    Q ∪ Finset.univ.biUnion R' = T ∪ Finset.univ.biUnion R ∧
    (∀ v, (R' v).card = (R v).card) ∧
    diameter ends Q ≤ ENNReal.ofReal (C * (B.card + (A.card : ℝ) / d)) ∧
    (((internal ends Q \ (A ∪ B)).card : ℕ) : ℝ) ≤ 2 * (B.card + (A.card : ℝ) / d) := by sorry

end LowDiameterNashWilliams.Main
