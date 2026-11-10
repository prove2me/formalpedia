-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_1
-- name    : HGASUndecidable.Main.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:35.822691+00:00
-- url     : https://prove2.me/theorems/3f9b88e9-b7a6-4734-b859-1b1237ab2c9a
-- title:
--   Theorem 2.1 — one many-one complete (resp. undecidable) HGAS(n*, 2k*+1) gives the same for all n ≥ C(n*+k*−1, k*), odd d ≥ 3; same for HLS with many-one hardness
-- statement:
--   The result includes four implications: completeness and undecidability transfer separately for HGAS, and many-one hardness and undecidability transfer separately for HLS. Theorem 2.1. Suppose there exist integers n∗ ≥ 1 and odd d∗ = 2k∗ + 1 ≥ 3 such that HGAS(n∗, d∗) is many-one complete (respectively, undecidable). Set N = \binom{n∗+k∗−1}{k∗}. Then for every n ≥ N and odd d ≥ 3, the set HGAS(n, d) is also many-one complete (respectively, undecidable). The same result holds for HLS and many-one hardness instead of HGAS and many-one completeness.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Theorem 2.1, printed p. 3 (PDF 5)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_2_1 (n₀ k₀ : ℕ) (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀) :
    ∀ n d : ℕ, Nat.choose (n₀+k₀-1) k₀ ≤ n → 3 ≤ d → Odd d →
      (ManyOneComplete (HGAS n₀ (2*k₀+1)) → ManyOneComplete (HGAS n d)) ∧
      (¬ComputablePred (HGAS n₀ (2*k₀+1)) → ¬ComputablePred (HGAS n d)) ∧
      (ManyOneHard (HLS n₀ (2*k₀+1)) → ManyOneHard (HLS n d)) ∧
      (¬ComputablePred (HLS n₀ (2*k₀+1)) → ¬ComputablePred (HLS n d)) := by sorry

end HGASUndecidable.Main
