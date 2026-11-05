-- Prove2me | Theorems.Thm_GaussianTensorExecution_cubeMap_zip
-- name    : GaussianTensorExecution.cubeMap_zip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.272597+00:00
-- url     : https://prove2.me/theorems/f8424c0e-bb21-4dea-99d8-1a37e3a47d63
-- title:
--   GaussianTensorExecution: Cube Map zip
-- statement:
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L71-L81). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L71-L81 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.cubeMap_zip (n : Nat) (f : GInt → GInt)
    (g : GInt → GInt → GInt) (h : ∀ u v, f (g u v) = g (f u) (f v))
    (u v : Cube n) :
    cubeMap f n (cubeZip g n u v) =
      cubeZip g n (cubeMap f n u) (cubeMap f n v) := by sorry
