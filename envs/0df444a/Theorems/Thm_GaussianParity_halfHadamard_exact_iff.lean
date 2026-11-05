-- Prove2me | Theorems.Thm_GaussianParity_halfHadamard_exact_iff
-- name    : GaussianParity.halfHadamard_exact_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/69a6fd11-66d7-47c6-8ca4-45827abc8c59
-- title:
--   DyadicCertificates: Half Hadamard exact iff
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L318-L330). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L318-L330 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.halfHadamard_exact_iff (u v : GInt) :
    (scaleTwo (halfHadamard u v).1 = add u v ∧
     scaleTwo (halfHadamard u v).2 = add u (neg v)) ↔
    (u.re % 2 = v.re % 2 ∧ u.im % 2 = v.im % 2) := by sorry
