-- Prove2me | Theorems.Thm_GaussianSynthesis_fresh_scatter_denominator_cancellation
-- name    : GaussianSynthesis.fresh_scatter_denominator_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/cc193fbc-e7dc-4940-a165-e2dd4be4dc40
-- title:
--   GaussianScalarCircuits: Fresh scatter denominator cancellation
-- statement:
--   Substituting the producer image cancels five of the apparent six binary denominator bits: W/64 = (selectedG-T)/2.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L183-L194). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L183-L194 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.fresh_scatter_denominator_cancellation
    (T selectedInsideG selectedOutsideG selectedD selectedB N k : Int)
    (hD : selectedD = k*T-selectedInsideG)
    (hB : selectedB = 2*selectedOutsideG)
    (hN : N = -32*T) :
    scatterNumerator64 selectedB selectedD N k =
      32*(selectedInsideG+selectedOutsideG-T) := by sorry
