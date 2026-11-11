-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_6_1
-- name    : LowDiameterNashWilliams.Main.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:56.293208+00:00
-- url     : https://prove2.me/theorems/ca841232-d019-401f-a3c9-2f04c9727f5d
-- title:
--   Lemma 6.1 — Minimum-degree refinement
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with minimum degree $\delta\ge2$, supplied with $k\ge1$ edge-disjoint spanning trees. There are absolute positive constants, a fixed polylogarithmic exponent $a$, and one randomized finite program producing $k$ edge-disjoint spanning trees, each satisfying both
--
--   $$\operatorname{diam}(T_i)\le C_Dn/\delta,\qquad |\operatorname{int}(T_i)|\le C_I(n/\delta)\log\delta.$$
--
--   Every halting output is correct, termination is almost sure, and expected charged time is at most
--
--   $$C_T(n^4+\delta^{7/2}n^{3/2}+\delta n^3)(1+\log n+\log(\delta+1))^a.$$
--
--   The actual minimum degree is computed from all host edges; those extra edges are available to the algorithm. Singleton local parts used inside its proof are valid one-vertex trees. This strengthens Proposition 1 to the parameter needed by the goal.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
--   - encoding: deterministic or randomized algorithm with the stated operation-time bound → one finite program and word coefficient before the inputs, charged published word-RAM execution, literal output masks, tail-sum extended expected cost or worst-case deterministic cost; reason: standard O(log n)-bit word operations from Section 4.4; no free algorithm calls, cost annotations or ignored retries; Lemma 4.2 additionally allows log d bits to read d
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 6.1, p. 24 (PDF p. 25)

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

theorem lemma_6_1 :
  ∃ C_D C_I C_T : ℝ, 0 < C_D ∧ 0 < C_I ∧ 0 < C_T ∧
  ∃ a c : ℕ, 0 < c ∧ ∃ P : Program, ∀ n m k : ℕ, 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m),
  Simple ends → 2 ≤ minDegree ends → Packing ends T →
  (∃ U : Trees k m, GoodPacking ends (C_D * ((n : ℝ) / minDegree ends))
    (C_I * ((n : ℝ) / minDegree ends) * Real.log (minDegree ends)) U) ∧
  Runs P (wordSize c n 0) (graphWords ends ++ [k] ++ treeWords T)
    (fun mem => ∃ U : Trees k m, Outputs mem (treeWords U) ∧
      GoodPacking ends (C_D * ((n : ℝ) / minDegree ends))
        (C_I * ((n : ℝ) / minDegree ends) * Real.log (minDegree ends)) U)
    (C_T * ((n : ℝ) ^ 4 + ((minDegree ends : ℝ) ^ (7 / 2 : ℝ)) *
      ((n : ℝ) ^ (3 / 2 : ℝ)) + minDegree ends * (n : ℝ) ^ 3) * soft a n (minDegree ends)) := by sorry

end LowDiameterNashWilliams.Main
