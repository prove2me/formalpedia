-- Prove2me | Theorems.Thm_GaussianTensorExecution_forward_binary_input_grid
-- name    : GaussianTensorExecution.forward_binary_input_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/d34c5798-9b35-4156-9204-9461e70511d6
-- title:
--   GaussianTensorExecution: Forward binary input grid
-- statement:
--   For incoming binary-grid precision p, the terminal recursive C tensor needs p+ceil(D/2) binary fractional bits. The Pi tag 2p represents the same binary grid, up to a unit phase.
--
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L380-L385). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L380-L385 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.forward_binary_input_grid (n p : Nat) (z : Cube n) (path : Path n) :
    ∃ w : GInt, piIter (2*p+n) w =
      scale ((2 : Int)^(p+(n+1)/2)) (get n (forward n z) path) := by sorry
