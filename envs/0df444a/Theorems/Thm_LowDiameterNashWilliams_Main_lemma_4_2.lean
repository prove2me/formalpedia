-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_2
-- name    : LowDiameterNashWilliams.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:44.491779+00:00
-- url     : https://prove2.me/theorems/a346f487-320a-4c3c-9235-91589fd33b7d
-- title:
--   Lemma 4.2 — Outdegree-preserving shortening
-- statement:
--   Let $T$ be a spanning tree of a simple graph on $N\ge1$ vertices, $X\subseteq V$, and $d\ge1$ an integer. Let $D$ orient the edges outside $T$ with outdegree at least $d$ at every vertex outside $X$. There are a spanning tree $Q$ and an orientation $D'$ of its complementary edges for which
--
--   $$\operatorname{diam}(Q)\le C_D(|X|+N/d),\qquad
--   \deg^+_{D'}(v)=\deg^+_D(v)\quad(v\in V).$$
--
--   A single deterministic finite program computes $Q,D'$ in at most $C_TdN^3$ charged operations, for absolute positive constants. The input includes $G,T,X,d,D$ and the output gives both $Q$ and $D'$. Singleton graphs and $X=V$ are included. This is the outdegree-preserving tool used to shorten a receiving tree.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
--   - encoding: deterministic or randomized algorithm with the stated operation-time bound → one finite program and word coefficient before the inputs, charged published word-RAM execution, literal output masks, tail-sum extended expected cost or worst-case deterministic cost; reason: standard O(log n)-bit word operations from Section 4.4; no free algorithm calls, cost annotations or ignored retries; Lemma 4.2 additionally allows log d bits to read d
--   - encoding: an orientation on the specified tree or complementary edge set → an endpoint-pair map on the ambient edge labels, constrained only on the oriented edge set; reason: unused values carry no condition and do not affect any outgoing count or execution guarantee
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 4.2, p. 12 (PDF p. 13)

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

theorem lemma_4_2 :
  ∃ C_D C_T : ℝ, 0 < C_D ∧ 0 < C_T ∧ ∃ c : ℕ, 0 < c ∧ ∃ P : Program,
  ∀ n m d : ℕ, 1 ≤ n → 1 ≤ d →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (X : Finset (Fin n)) (D : Direction n m),
  Simple ends → IsSpanningTree ends T → Orients ends (Finset.univ \ T) D →
  (∀ v, v ∉ X → d ≤ outdegree (Finset.univ \ T) D v) →
  (∃ (Q : Edges m) (D' : Direction n m), IsSpanningTree ends Q ∧
    Orients ends (Finset.univ \ Q) D' ∧
    diameter ends Q ≤ ENNReal.ofReal (C_D * (X.card + (n : ℝ) / d)) ∧
    ∀ v, outdegree (Finset.univ \ Q) D' v = outdegree (Finset.univ \ T) D v) ∧
  RunsDet P (wordSize c n d)
    (graphWords ends ++ [d] ++ setWords T ++ setWords X ++ directionWords D)
    (fun mem => ∃ (Q : Edges m) (D' : Direction n m),
      Outputs mem (setWords Q ++ directionWords D') ∧ IsSpanningTree ends Q ∧
      Orients ends (Finset.univ \ Q) D' ∧
      diameter ends Q ≤ ENNReal.ofReal (C_D * (X.card + (n : ℝ) / d)) ∧
      ∀ v, outdegree (Finset.univ \ Q) D' v = outdegree (Finset.univ \ T) D v)
    (C_T * d * (n : ℝ) ^ 3) := by sorry

end LowDiameterNashWilliams.Main
