-- Prove2me | Theorems.Thm_GaussianParity_butterfly_exact
-- name    : GaussianParity.butterfly_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/b198d3cc-573a-4b28-8fc8-aad718f60305
-- title:
--   DyadicCertificates: Butterfly exact
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L64-L68). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L64-L68 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.butterfly_exact (u v : GInt) (h : SameResidue u v) :
    mulPi (butterfly u v).1 = numeratorLeft u v ∧
    mulPi (butterfly u v).2 = numeratorRight u v := by sorry
