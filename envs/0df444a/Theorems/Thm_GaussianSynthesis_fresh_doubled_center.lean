-- Prove2me | Theorems.Thm_GaussianSynthesis_fresh_doubled_center
-- name    : GaussianSynthesis.fresh_doubled_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.00224+00:00
-- url     : https://prove2.me/theorems/e31603bd-fd4d-4f79-bd4d-d43c95146678
-- title:
--   GaussianScalarCircuits: Fresh doubled center
-- statement:
--   A doubled incidence center can likewise be halved exactly on the image.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L174-L175). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L174-L175 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis

theorem GaussianSynthesis.fresh_doubled_center (G B : Int) (h : B = 2*G) : B/2 = G := by sorry
