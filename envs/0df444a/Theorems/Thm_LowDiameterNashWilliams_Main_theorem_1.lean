-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_theorem_1
-- name    : LowDiameterNashWilliams.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:52.881609+00:00
-- url     : https://prove2.me/theorems/7fea3acf-4795-4894-bc5e-e3fbafc7037a
-- title:
--   Theorem 1 — Low-diameter Nash-Williams–Tutte theorem
-- statement:
--   Let $G$ be a simple graph on $n\ge2$ vertices with minimum degree $\delta$, and let $k\ge1$. It has $k$ edge-disjoint spanning trees if and only if every partition $\mathcal P$ of its vertex set into nonempty blocks satisfies
--
--   $$e_G(\mathcal P)\ge k(|\mathcal P|-1).$$
--
--   There are absolute positive constants $C_D,C_I,C_T$, a fixed nonnegative integer $a$, a fixed word coefficient, and one finite randomized program, all chosen before $G,n,k,\delta$. Whenever the partition condition holds, one family of exactly $k$ edge-disjoint spanning trees satisfies, simultaneously for every $i$,
--
--   $$\operatorname{diam}(T_i)\le C_Dn/\delta,\qquad |\operatorname{int}(T_i)|\le C_I(n/\delta)\log(\delta+1).$$
--
--   Given only the adjacency-list graph and $k$, the program terminates almost surely, every halting output is such a family, and its expected charged time is at most
--
--   $$C_Tn^5(1+\log n)^a.$$
--
--   Both directions of the partition characterization hold on the full domain, and the construction is conditional on that condition. It implies $\delta\ge k\ge1$; no large-k or $\delta\ge2$ hypothesis is imposed. This is the complete goal, combining the classical criterion with simultaneous geometry and actual computation.
--
--   Differences from the source:
--   - encoding: finite simple graph and its finite undirected edge sets → vertices Fin n, edges Fin m, injective loopless unordered endpoints and the published tree predicates; reason: finite labelling preserves every graph instance, and tree partitions cover all host edges exactly
--   - encoding: absolute O bounds and, where stated, sufficiently large k → positive constants and any k threshold are existentially quantified before all input data; reason: explicit expansion of the source asymptotics; one constant can dominate the finitely many constants in one result
--   - encoding: shortest-path tree diameter measured in edges → extended nonnegative infimum of walk lengths and supremum over vertex pairs; reason: on every asserted spanning tree this is the finite ordinary diameter, including singleton diameter zero
--   - encoding: deterministic or randomized algorithm with the stated operation-time bound → one finite program and word coefficient before the inputs, charged published word-RAM execution, literal output masks, tail-sum extended expected cost or worst-case deterministic cost; reason: standard O(log n)-bit word operations from Section 4.4; no free algorithm calls, cost annotations or ignored retries; Lemma 4.2 additionally allows log d bits to read d
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 1, p. 1 (PDF p. 2)

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

theorem theorem_1 :
  ∃ C_D C_I C_T : ℝ, 0 < C_D ∧ 0 < C_I ∧ 0 < C_T ∧
  ∃ a c : ℕ, 0 < c ∧ ∃ P : Program, ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ ends : Fin m → Sym2 (Fin n), Simple ends →
  ((∃ T : Trees k m, Packing ends T) ↔ IsAdmissible k ends) ∧
  (IsAdmissible k ends →
    (∃ U : Trees k m, GoodPacking ends (C_D * ((n : ℝ) / minDegree ends))
      (C_I * ((n : ℝ) / minDegree ends) * Real.log (minDegree ends + 1)) U) ∧
    Runs P (wordSize c n 0) (graphWords ends ++ [k])
      (fun mem => ∃ U : Trees k m, Outputs mem (treeWords U) ∧
        GoodPacking ends (C_D * ((n : ℝ) / minDegree ends))
          (C_I * ((n : ℝ) / minDegree ends) * Real.log (minDegree ends + 1)) U)
      (C_T * (n : ℝ) ^ 5 * (1 + Real.log n) ^ a)) := by sorry

end LowDiameterNashWilliams.Main
