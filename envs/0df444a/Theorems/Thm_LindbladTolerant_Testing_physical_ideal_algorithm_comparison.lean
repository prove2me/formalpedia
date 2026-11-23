-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_physical_ideal_algorithm_comparison
-- name    : LindbladTolerant.Testing.physical_ideal_algorithm_comparison
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:15.618808+00:00
-- url     : https://prove2.me/theorems/8be9fee6-2ab3-4c50-b6dc-ae584f66edcc
-- title:
--   Theorem 5.1 — physical versus ideal output laws
-- statement:
--   For either binary answer $b$, the physical Algorithm 1 output probability and its ideal flagged-preparation counterpart differ by at most $1/32$:
--
--   $$
--   \left|\Pr_{\mathrm{physical}}[b]-\Pr_{\mathrm{ideal}}[b]\right|\le \frac1{32}.
--   $$
--
--   The bound is uniform over the source class and uses the actual finite-time success blocks, not an assumption that they are ideal jump states. It is the data-processing consequence of the tensor-product trace-distance estimate in the proof of Theorem 5.1.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.1 proof, p.28, Eqs.(106)–(109).

import Definitions.Def_LindbladTolerant_Testing_ideal_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

theorem LindbladTolerant.Testing.physical_ideal_algorithm_comparison {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (bound eps1 eps2 : ℝ) (hbound : 0 < bound) (he1 : 0 ≤ eps1)
    (he12 : eps1 < eps2) (he2 : eps2 ≤ bound / Real.sqrt 2)
    (g : Super (Qubits n) (Qubits n)) (hg : SourceClass k bound g) (b : Bool) :
    |algorithmProbability k bound eps1 eps2 g b -
      idealAlgorithmProbability k bound eps1 eps2 g b| ≤ 1/32 := by sorry
