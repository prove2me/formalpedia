-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_1_1
-- name    : HGASUndecidable.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:38.071272+00:00
-- url     : https://prove2.me/theorems/3a25f251-4c92-4881-9caa-cda396252dc3
-- title:
--   Theorem 1.1 — GAS is many-one complete in every sufficiently large dimension
-- statement:
--   Theorem 1.1. There is an integer N ≥ 1 such that for every n ≥ N and every odd d ≥ 3, the set HGAS(n, d) is many-one complete (and hence undecidable).
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Theorem 1.1, printed p. 1 (PDF 3)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_1_1 : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ d : ℕ, 3 ≤ d → Odd d → ManyOneComplete (HGAS n d) ∧ ¬ComputablePred (HGAS n d) := by sorry

end HGASUndecidable.Main
