-- Prove2me | Theorems.Thm_GaussianParity_odd_ideal_parity
-- name    : GaussianParity.odd_ideal_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/e1576ad0-9b1e-427e-83f1-0695cacb37fb
-- title:
--   GaussianLattice: Odd ideal parity
-- statement:
--   Coordinate parity is the one-bit constraint in the odd ideal.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L111-L114). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L111-L114 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.odd_ideal_parity (q : Nat) (z : GInt)
    (h : PiPowerDivisible (2*q+1) z) :
    ∃ w : GInt, scale ((2 : Int)^q) w = z ∧ w.re % 2 = w.im % 2 := by sorry
