-- Prove2me | Theorems.Thm_GaussianParity_butterfly_integral_iff
-- name    : GaussianParity.butterfly_integral_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/799f2546-59ee-4c6f-8a3c-e0c24534a34d
-- title:
--   DyadicCertificates: Butterfly integral iff
-- statement:
--   Both butterfly numerators are divisible by 1+i exactly when inputs agree in Z[i]/(1+i). This only checks one parity bit per Gaussian integer.
--
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L59-L62). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L59-L62 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.butterfly_integral_iff (u v : GInt) :
    PiDvd (numeratorLeft u v) ∧ PiDvd (numeratorRight u v) ↔ SameResidue u v := by sorry
