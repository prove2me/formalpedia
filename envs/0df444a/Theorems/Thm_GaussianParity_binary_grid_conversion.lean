-- Prove2me | Theorems.Thm_GaussianParity_binary_grid_conversion
-- name    : GaussianParity.binary_grid_conversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/272bfa1d-e848-445b-ac65-9d860e69341b
-- title:
--   GaussianLattice: Binary grid conversion
-- statement:
--   Full denominator upper bound for every π^{-D} Gaussian numerator. The equation says z/π^D = w/2^ceil(D/2), with no rational arithmetic assumptions.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L173-L194). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L173-L194 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.binary_grid_conversion (D : Nat) (z : GInt) :
    ∃ w : GInt, repeatPi D w = scale ((2 : Int)^((D+1)/2)) z := by sorry
