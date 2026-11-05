-- Prove2me | Theorems.Thm_GaussianSynthesis_corrected_scatter_sum_exact
-- name    : GaussianSynthesis.corrected_scatter_sum_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/9300d07d-fe32-4abb-a870-b185ddc478a8
-- title:
--   GaussianScalarCircuits: Corrected scatter sum exact
-- statement:
--   Arbitrary fresh scalar input values superpose exactly; the only hypothesis is that each triple intersection size lies between zero and three.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L332-L344). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L332-L344 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.corrected_scatter_sum_exact (xs : List (Int × Int))
    (hj : ∀ entry ∈ xs, 0 ≤ entry.2 ∧ entry.2 ≤ 3) :
    sumCorrectedScatter64 xs = 64*sumDiagonalSources xs := by sorry
