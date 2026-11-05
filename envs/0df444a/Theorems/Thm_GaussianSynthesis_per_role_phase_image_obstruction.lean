-- Prove2me | Theorems.Thm_GaussianSynthesis_per_role_phase_image_obstruction
-- name    : GaussianSynthesis.per_role_phase_image_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/9d160433-2b00-44aa-88e6-962b6c0b4754
-- title:
--   GaussianScalarCircuits: Per role phase image obstruction
-- statement:
--   In the actual fresh impulse (0,1,19), changing only B19 from 2 to 2i adds (-2+2i) to the fresh N=-32. Old/new phases may agree within each role while these unequal inter-role phases destroy the producer image.
--
--   Canonical Gaussian arithmetic, scalar circuit normalization and exact refinement lemmas.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L620-L629). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianScalarCircuits.lean#L620-L629 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
set_option autoImplicit true
open GaussianSynthesis
open GaussianParity

theorem GaussianSynthesis.per_role_phase_image_obstruction :
    add ⟨-32,0⟩ (gaussianDifference ⟨0,2⟩ ⟨2,0⟩) = ⟨-34,2⟩ ∧
    ¬ ∃ t : GInt, add ⟨-32,0⟩ (gaussianDifference ⟨0,2⟩ ⟨2,0⟩)
      = scale (-32) t := by sorry
