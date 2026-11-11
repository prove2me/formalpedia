-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_1
-- name    : LowDiameterNashWilliams.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:46.661994+00:00
-- url     : https://prove2.me/theorems/8e2e6411-4f18-463a-8738-5a535d7732ef
-- title:
--   Lemma 3.1 — Minimum-weight extraction
-- statement:
--   Let a simple $n$-vertex graph, $n\ge2$, have its edges partitioned into $k\ge1$ spanning trees oriented toward $r$. Let $L\subseteq V$ and assume every vertex has at most $k/8$ outgoing neighbors in $L$. Put $w(e)=|e\cap L|$. If $T$ minimizes $w(E(T))$ among spanning trees whose deletion leaves an exact partition into $k-1$ spanning trees, then an absolute $C>0$ gives
--
--   $$|\operatorname{int}(T)\cap L|\le Cn/k.$$
--
--   The minimum is taken only among eligible trees, rather than unrestricted spanning trees. This extraction preserves a partition of all residual edges for the following rounds.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: an orientation on the specified tree or complementary edge set → an endpoint-pair map on the ambient edge labels, constrained only on the oriented edge set; reason: unused values carry no condition and do not affect any outgoing count or execution guarantee
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 3.1, p. 5 (PDF p. 6)

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

theorem lemma_3_1 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) (L : Finset (Fin n)) (Q : Edges m),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
  (∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) →
  Extractable ends k Q →
  (∀ U : Edges m, Extractable ends k U →
    weight (incidenceWeight ends L) Q ≤ weight (incidenceWeight ends L) U) →
    (((internal ends Q ∩ L).card : ℕ) : ℝ) ≤ C * ((n : ℝ) / k) := by sorry

end LowDiameterNashWilliams.Main
