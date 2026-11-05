-- Prove2me | Theorems.Thm_GaussianParity_scale_injective
-- name    : GaussianParity.scale_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/7d2d3a8d-10d4-4e51-8ac2-568391f81f22
-- title:
--   GaussianLattice: Scale injective
-- statement:
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L242-L250). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L242-L250 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.scale_injective (k : Int) (hk : k ≠ 0) {u v : GInt}
    (h : scale k u = scale k v) : u = v := by sorry
