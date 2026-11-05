-- Prove2me | Theorems.Thm_GaussianSynthesis_dirty_update_difference_image
-- name    : GaussianSynthesis.dirty_update_difference_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/08b19d89-5a1f-4bee-b317-a981141fb7df
-- title:
--   GaussianScalarCircuits: Dirty update difference image
-- statement:
--   Dirty scratch may be arbitrary. Its update difference, rather than its raw contents, has the fresh producer invariant.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L282-L289). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L282-L289 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.dirty_update_difference_image (oldD oldB : Int) (xs : List (Int × Int)) :
    mixedCenterN
      ((oldB+(sumCenterColumns xs).sumB)-oldB)
      ((oldD+(sumCenterColumns xs).sumD)-oldD)
      = -32*(sumCenterColumns xs).total := by sorry
