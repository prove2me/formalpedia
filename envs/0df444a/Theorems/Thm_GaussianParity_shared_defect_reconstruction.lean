-- Prove2me | Theorems.Thm_GaussianParity_shared_defect_reconstruction
-- name    : GaussianParity.shared_defect_reconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/ecc1acb4-a40d-4590-a89d-16811484ffb4
-- title:
--   DyadicCertificates: Shared defect reconstruction
-- statement:
--   Euclidean integer quotients plus the shared bit reconstruct all four numerators of twice C. This is an exact identity, including negative inputs.
--
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L295-L303). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L295-L303 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.shared_defect_reconstruction (u v : GInt) :
    let n := doubleButterfly u v
    let epsilon := sharedDefect u v
    n.1.re = 2 * (n.1.re / 2) + epsilon ∧
    n.1.im = 2 * (n.1.im / 2) + epsilon ∧
    n.2.re = 2 * (n.2.re / 2) + epsilon ∧
    n.2.im = 2 * (n.2.im / 2) + epsilon := by sorry
