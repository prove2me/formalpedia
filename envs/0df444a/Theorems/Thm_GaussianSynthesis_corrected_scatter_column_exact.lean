-- Prove2me | Theorems.Thm_GaussianSynthesis_corrected_scatter_column_exact
-- name    : GaussianSynthesis.corrected_scatter_column_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/60aa744d-8190-4c4f-90c6-3edd8138f61b
-- title:
--   GaussianScalarCircuits: Corrected scatter column exact
-- statement:
--   With the actual disjoint and intersection-two side terms, each column of the collected scatter is 64 times its diagonal source value.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L315-L320). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L315-L320 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.corrected_scatter_column_exact (x j : Int) (hj : 0 ≤ j ∧ j ≤ 3) :
    correctedScatterColumn64 x j = 64*(if j=3 then x else 0) := by sorry
