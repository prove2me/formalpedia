-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_3
-- name    : LowDiameterNashWilliams.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:41.15511+00:00
-- url     : https://prove2.me/theorems/92d75ea8-ed3e-4bbf-84a7-b721d55251e2
-- title:
--   Lemma 3.3 — Integer-weight inequality
-- statement:
--   Let the edges of a simple $n$-vertex graph, $n\ge2$, be partitioned into $k\ge8$ spanning trees oriented toward $r$. Let $L\subseteq V$, suppose every vertex has at most $k/8$ outgoing neighbors in $L$, and put $w(e)=|e\cap L|$. For any integer edge weight $f$, write $\mu(f)$ for the maximum $f$-weight of a spanning tree. There is an absolute $C>0$ such that every integer weight $p$ satisfies
--
--   $$p(E)-(k-1)\mu(p)-\mu(p-w)\le |L|+Cn/k.$$
--
--   The weight maximum ranges over all host spanning trees, and the input partition ensures that family is nonempty. This is the dual weight estimate used in minimum-weight extraction.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: an orientation on the specified tree or complementary edge set → an endpoint-pair map on the ambient edge labels, constrained only on the oriented edge set; reason: unused values carry no condition and do not affect any outgoing count or execution guarantee
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 3.3, p. 7 (PDF p. 8)

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

theorem lemma_3_3 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 8 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) (L : Finset (Fin n)),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
  (∀ v, (outgoingTo T D v L : ℝ) ≤ (k : ℝ) / 8) → ∀ p : Fin m → ℤ,
    ((weight p Finset.univ - ((k : ℤ) - 1) * maxTreeWeight ends p -
      maxTreeWeight ends (fun e => p e - incidenceWeight ends L e) : ℤ) : ℝ) ≤
        L.card + C * ((n : ℝ) / k) := by sorry

end LowDiameterNashWilliams.Main
