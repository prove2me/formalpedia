-- Prove2me | Theorems.Thm_MatrixMatchingDual_exact_dual_certificate_optimal
-- name    : MatrixMatchingDual.exact_dual_certificate_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/45c424bb-6305-4150-b683-b40bdfe3f480
-- title:
--   MatchingDual: Exact dual certificate optimal
-- statement:
--   Equality of a checked candidate cost to the dual objective certifies optimality for that exact integer cost objective, given any alternative's same-row and complete-column matching contracts.
--
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L85-L94). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L85-L94 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_MatchingDual
set_option autoImplicit true
open MatrixMatchingDual

theorem MatrixMatchingDual.exact_dual_certificate_optimal (candidateCost rowTotal : Int)
    (allPrices : List Int) (hcertificate : candidateCost = rowTotal+allPrices.sum)
    (alternative : List Edge) (unused : List Int)
    (hedge : ∀ e ∈ alternative, e.rowPrice+e.columnPrice ≤ e.cost)
    (hunused : ∀ p ∈ unused, p ≤ 0)
    (hpartition : List.Perm ((alternative.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum alternative = rowTotal) :
    candidateCost ≤ costSum alternative := by sorry
