-- Prove2me | Theorems.Thm_GaussianSynthesis_mixed_center_image
-- name    : GaussianSynthesis.mixed_center_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/a700dc01-3f0b-4556-92be-acab14666212
-- title:
--   GaussianScalarCircuits: Mixed center image
-- statement:
--   The actual 19+9 center split has image identity N=-32T.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L155-L161). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L155-L161 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.mixed_center_image (T sumInsideG sumOutsideG sumD sumB : Int)
    (hG : sumInsideG + sumOutsideG = 3*T)
    (hD : sumD = 19*T-sumInsideG)
    (hB : sumB = 2*sumOutsideG) :
    mixedCenterN sumB sumD = -32*T := by sorry
