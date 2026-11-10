-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_3
-- name    : HGASUndecidable.Main.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:36.963083+00:00
-- url     : https://prove2.me/theorems/2fccfe40-6bc2-4172-a931-09fb99b05724
-- title:
--   Theorem 2.3 — some HGAS(n*, d*) with d* odd ≥ 3 is many-one complete (proof p. 69, PDF 71)
-- statement:
--   Theorem 2.3. There exist an integer n∗ ≥ 1 and an odd integer d∗ ≥ 3 such that HGAS(n∗, d∗) is many-one complete.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Theorem 2.3, printed p. 3 (PDF 5)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem theorem_2_3 : ∃ n d : ℕ, 1 ≤ n ∧ 3 ≤ d ∧ Odd d ∧ ManyOneComplete (HGAS n d) := by sorry

end HGASUndecidable.Main
