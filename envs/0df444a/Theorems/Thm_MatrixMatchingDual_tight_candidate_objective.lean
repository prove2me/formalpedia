-- Prove2me | Theorems.Thm_MatrixMatchingDual_tight_candidate_objective
-- name    : MatrixMatchingDual.tight_candidate_objective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/eb9d908f-21fb-4fc9-9819-7fcd8dbd08d2
-- title:
--   MatchingDual: Tight candidate objective
-- statement:
--   Selected tight inequalities plus zero unused prices give the required exact equality of the primal candidate and dual objectives.
--
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L124-L136). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L124-L136 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_MatchingDual
set_option autoImplicit true
open MatrixMatchingDual

theorem MatrixMatchingDual.tight_candidate_objective (candidate : List Edge) (unused allPrices : List Int)
    (rowTotal : Int)
    (htight : ∀ e ∈ candidate, e.rowPrice+e.columnPrice = e.cost)
    (hzero : ∀ p ∈ unused, p = 0)
    (hpartition : List.Perm ((candidate.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum candidate = rowTotal) :
      costSum candidate = rowTotal+allPrices.sum := by sorry
