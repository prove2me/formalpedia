-- Prove2me | Theorems.Thm_HGASUndecidable_Main_proposition_4_4
-- name    : HGASUndecidable.Main.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:30.13548+00:00
-- url     : https://prove2.me/theorems/9dfcbd33-d03b-40ff-b22c-2968067f20fb
-- title:
--   Proposition 4.4 — HGAS is r.e.; so are HGAS(n, d) and HGAS(·, d)
-- statement:
--   Proposition 4.4 (Recursive enumerability of GAS). HGAS is recursively enumerable. Consequently, so are HGAS(n, d) and HGAS(·, d) for all fixed n, d.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: one fixed reasonable code for rational homogeneous polynomial vector fields → Encodable encoding of (dimension, declared degree, finite coordinate/exponent-list/rational-coefficient triples), with normalized support validation; reason: all rational fields have such finite representations; duplicate monomials are combined and invalid codes are negative instances
--   - encoding: Turing-machine recursive enumerability and total computability → Mathlib REPred, ComputablePred, Computable, and ManyOneReducible using partial recursive functions; reason: these are equivalent computability notions under effective translations
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Proposition 4.4, printed p. 23 (PDF 25)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem proposition_4_4 : REPred HGASall ∧
    (∀ n d, REPred (HGAS n d)) ∧ (∀ d, REPred (HGASdegree d)) := by sorry

end HGASUndecidable.Main
