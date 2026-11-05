-- Prove2me | Theorems.Thm_GaussianParity_gaussianMul_pi_pi
-- name    : GaussianParity.gaussianMul_pi_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/b3f0b4ec-1d12-4aba-93ae-685fc7d87c5d
-- title:
--   GaussianLattice: Gaussian Mul pi pi
-- statement:
--   Multiplying two π factors contributes one full binary bit, together with a unit phase. This is the normalization cancellation at odd depth.
--
--   Gaussian divisibility, lattice and binary-grid conversion lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L288-L290). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianLattice.lean#L288-L290 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.gaussianMul_pi_pi (u v : GInt) :
    gaussianMul (mulPi u) (mulPi v) = scale 2 (mulI (gaussianMul u v)) := by sorry
