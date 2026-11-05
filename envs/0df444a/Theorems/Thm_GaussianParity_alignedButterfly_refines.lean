-- Prove2me | Theorems.Thm_GaussianParity_alignedButterfly_refines
-- name    : GaussianParity.alignedButterfly_refines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/21d75009-204b-43f0-bdb7-4f1b9755f7ff
-- title:
--   DyadicCertificates: Aligned Butterfly refines
-- statement:
--   Exact Gaussian-integer parity and dyadic butterfly certificates.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L364-L371). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/DyadicCertificates.lean#L364-L371 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_DyadicCertificates
set_option autoImplicit true
open GaussianParity

theorem GaussianParity.alignedButterfly_refines (x y : Fraction) :
    let e := commonExponent x y
    let u := (raiseTo x e).numerator
    let v := (raiseTo y e).numerator
    let p := alignedButterfly x y
    SameValue ⟨p.left, p.exponent⟩ ⟨numeratorLeft u v, e + 1⟩ ∧
    SameValue ⟨p.right, p.exponent⟩ ⟨numeratorRight u v, e + 1⟩ := by sorry
