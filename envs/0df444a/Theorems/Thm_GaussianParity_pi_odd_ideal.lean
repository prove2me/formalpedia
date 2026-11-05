-- Prove2me | Theorems.Thm_GaussianParity_pi_odd_ideal
-- name    : GaussianParity.pi_odd_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/7f95f2cd-db1a-4a53-a908-a3b1844c8061
-- title:
--   GaussianLattice: Pi odd ideal
-- statement:
--   The odd π-power ideal is the binary-power ideal restricted by one Gaussian parity bit.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L97-L108). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L97-L108 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.pi_odd_ideal (q : Nat) (z : GInt) :
    PiPowerDivisible (2*q+1) z ↔
      ∃ w : GInt, scale ((2 : Int)^q) w = z ∧ PiDvd w := by sorry
