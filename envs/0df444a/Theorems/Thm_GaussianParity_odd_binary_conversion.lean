-- Prove2me | Theorems.Thm_GaussianParity_odd_binary_conversion
-- name    : GaussianParity.odd_binary_conversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/215d3421-bf8d-41cf-9e62-fe4e57bb1f5b
-- title:
--   GaussianLattice: Odd binary conversion
-- statement:
--   The inverse conversion at an odd level uses one additional π factor. This certifies the exact fraction identity using cross multiplication only.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L143-L152). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L143-L152 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.odd_binary_conversion (q : Nat) (z : GInt) :
    repeatPi (2*q+1) (repeatNegI (q+1) (mulPi z)) =
      scale ((2 : Int)^(q+1)) z := by sorry
