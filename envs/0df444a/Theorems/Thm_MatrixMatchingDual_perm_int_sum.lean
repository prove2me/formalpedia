-- Prove2me | Theorems.Thm_MatrixMatchingDual_perm_int_sum
-- name    : MatrixMatchingDual.perm_int_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/b4be659b-e13b-45c1-ad86-b312af14671a
-- title:
--   MatchingDual: Perm int sum
-- statement:
--   Exact permutation preserves a column-price sum.
--
--   Weak duality and optimality certificates for finite weighted matching.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L22-L27). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/matrix-exponent-synthesis/MatchingDual.lean#L22-L27 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_MatchingDual
set_option autoImplicit true
open MatrixMatchingDual

theorem MatrixMatchingDual.perm_int_sum {xs ys : List Int} (h : List.Perm xs ys) : xs.sum = ys.sum := by sorry
