-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_3_2
-- name    : LowDiameterNashWilliams.Main.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:37.694202+00:00
-- url     : https://prove2.me/theorems/8067003d-4c05-47a1-8943-c2c17bad2a56
-- title:
--   Lemma 3.2 — Tight-set exceptional vertices
-- statement:
--   Let $G$ be a simple graph on $n\ge2$ vertices with an exact partition into $k\ge1$ spanning trees oriented toward a vertex $r$. A nonempty set $A$ is tight when it induces exactly $k(|A|-1)$ edges and is nontrivial when $|A|\ge2$. Let $R$ contain $r$ and every vertex $v$ lying in some nontrivial tight set $A$ with at least $3k/4$ outgoing arcs from $v$ to $V\setminus A$. There is an absolute $C>0$ such that
--
--   $$|R|\le Cn/k.$$
--
--   The bound isolates the exceptional vertices used in the weight inequality.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: an orientation on the specified tree or complementary edge set → an endpoint-pair map on the ambient edge labels, constrained only on the oriented edge set; reason: unused values carry no condition and do not affect any outgoing count or execution guarantee
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 3.2, p. 6 (PDF p. 7)

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

theorem lemma_3_2 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
    ((exceptional ends T D r).card : ℝ) ≤ C * ((n : ℝ) / k) := by sorry

end LowDiameterNashWilliams.Main
