-- Prove2me | Theorems.Thm_MatrixMatchingDual_matching_weak_duality
-- name    : MatrixMatchingDual.matching_weak_duality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/d6686e45-45fa-4839-b76f-8cfbbd3e013e
-- title:
--   MatchingDual: Matching weak duality
-- statement:
--   Weak duality against every matching whose selected and unused prices partition all columns and whose rows cover the same fixed row-price total.
--
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L68-L80). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L68-L80 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_MatchingDual
set_option autoImplicit true
open MatrixMatchingDual

theorem MatrixMatchingDual.matching_weak_duality (edges : List Edge) (unused allPrices : List Int)
    (rowTotal : Int)
    (hedge : ∀ e ∈ edges, e.rowPrice+e.columnPrice ≤ e.cost)
    (hunused : ∀ p ∈ unused, p ≤ 0)
    (hpartition : List.Perm ((edges.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum edges = rowTotal) :
    rowTotal+allPrices.sum ≤ costSum edges := by sorry
