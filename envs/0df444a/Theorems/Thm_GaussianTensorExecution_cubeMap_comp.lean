-- Prove2me | Theorems.Thm_GaussianTensorExecution_cubeMap_comp
-- name    : GaussianTensorExecution.cubeMap_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/7dff9ab5-84c9-4351-b5b3-9f0f0d7f32cf
-- title:
--   GaussianTensorExecution: Cube Map comp
-- statement:
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L62-L69). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L62-L69 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.cubeMap_comp (n : Nat) (f g : GInt → GInt) (z : Cube n) :
    cubeMap f n (cubeMap g n z) = cubeMap (fun u => f (g u)) n z := by sorry
