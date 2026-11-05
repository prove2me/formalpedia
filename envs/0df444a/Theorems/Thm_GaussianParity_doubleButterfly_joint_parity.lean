-- Prove2me | Theorems.Thm_GaussianParity_doubleButterfly_joint_parity
-- name    : GaussianParity.doubleButterfly_joint_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/7d8b1fb5-b23d-4994-84d1-c8fc3cd58c07
-- title:
--   DyadicCertificates: Double Butterfly joint parity
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L272-L278). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L272-L278 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.doubleButterfly_joint_parity (u v : GInt) :
    (doubleButterfly u v).1.re % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).1.im % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).2.re % 2 = (u.re + u.im + v.re + v.im) % 2 ∧
    (doubleButterfly u v).2.im % 2 = (u.re + u.im + v.re + v.im) % 2 := by sorry
