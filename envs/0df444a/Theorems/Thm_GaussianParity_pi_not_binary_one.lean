-- Prove2me | Theorems.Thm_GaussianParity_pi_not_binary_one
-- name    : GaussianParity.pi_not_binary_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/e207f3c5-75c5-4663-a031-9523fcabb702
-- title:
--   GaussianLattice: Pi not binary one
-- statement:
--   The next π level is not equivalent to one full binary bit: π itself has odd coordinates, while every multiple of 2 has even coordinates.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L118-L125). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L118-L125 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.pi_not_binary_one :
    PiPowerDivisible 1 ⟨1,1⟩ ∧ ¬ BinaryDivisible 1 ⟨1,1⟩ := by sorry
