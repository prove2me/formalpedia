-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_proposition_1
-- name    : LowDiameterNashWilliams.Main.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:33.820193+00:00
-- url     : https://prove2.me/theorems/b4e0ec03-d4d3-4f0a-925f-e2e1d29431fe
-- title:
--   Proposition 1 — All k trees with k-sensitive bounds
-- statement:
--   Let $G$ be a simple graph on $n\ge2$ vertices, supplied with $k\ge1$ edge-disjoint spanning trees. There are absolute positive constants $C_D,C_I,C_T$, a fixed polylogarithmic exponent $a$, and a single randomized finite program producing $k$ edge-disjoint spanning trees satisfying simultaneously, for every $i$,
--
--   $$\operatorname{diam}(T_i)\le C_Dn/k,\qquad |\operatorname{int}(T_i)|\le C_I(n/k)\log(k+1).$$
--
--   It terminates almost surely, every halting output is correct, and expected charged time is bounded by
--
--   $$C_T(k^{7/2}n^{3/2}+kn^3)(1+\log n+\log(k+1))^a.$$
--
--   The input graph may contain extra edges beyond the supplied trees. The same output family satisfies both bounds and retains all $k$ trees; the result supplies the k-sensitive construction used in the degree refinement.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
--   - encoding: deterministic or randomized algorithm with the stated operation-time bound → one finite program and word coefficient before the inputs, charged published word-RAM execution, literal output masks, tail-sum extended expected cost or worst-case deterministic cost; reason: standard O(log n)-bit word operations from Section 4.4; no free algorithm calls, cost annotations or ignored retries; Lemma 4.2 additionally allows log d bits to read d
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Proposition 1, p. 24 (PDF p. 25)

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

theorem proposition_1 :
  ∃ C_D C_I C_T : ℝ, 0 < C_D ∧ 0 < C_I ∧ 0 < C_T ∧
  ∃ a c : ℕ, 0 < c ∧ ∃ P : Program, ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m), Simple ends → Packing ends T →
  (∃ U : Trees k m, GoodPacking ends (C_D * ((n : ℝ) / k))
    (C_I * ((n : ℝ) / k) * Real.log (k + 1)) U) ∧
  Runs P (wordSize c n 0) (graphWords ends ++ [k] ++ treeWords T)
    (fun mem => ∃ U : Trees k m, Outputs mem (treeWords U) ∧
      GoodPacking ends (C_D * ((n : ℝ) / k))
        (C_I * ((n : ℝ) / k) * Real.log (k + 1)) U)
    (C_T * (((k : ℝ) ^ (7 / 2 : ℝ)) * ((n : ℝ) ^ (3 / 2 : ℝ)) + k * (n : ℝ) ^ 3) * soft a n k) := by sorry

end LowDiameterNashWilliams.Main
