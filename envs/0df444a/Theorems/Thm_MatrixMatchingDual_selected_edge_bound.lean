-- Prove2me | Theorems.Thm_MatrixMatchingDual_selected_edge_bound
-- name    : MatrixMatchingDual.selected_edge_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/b2bf8073-d377-4f4c-ad43-cdb8b95ba173
-- title:
--   MatchingDual: Selected edge bound
-- statement:
--   Summing the selected all-edge dual inequalities bounds the matching cost.
--
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L43-L55). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L43-L55 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_MatchingDual
set_option autoImplicit true
open MatrixMatchingDual

theorem MatrixMatchingDual.selected_edge_bound (edges : List Edge)
    (h : ∀ e ∈ edges, e.rowPrice+e.columnPrice ≤ e.cost) :
    rowSum edges+selectedSum edges ≤ costSum edges := by sorry
