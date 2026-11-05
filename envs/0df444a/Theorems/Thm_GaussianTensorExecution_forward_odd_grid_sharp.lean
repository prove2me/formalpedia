-- Prove2me | Theorems.Thm_GaussianTensorExecution_forward_odd_grid_sharp
-- name    : GaussianTensorExecution.forward_odd_grid_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/26300140-d806-4bbd-8a6b-986ae365cd0b
-- title:
--   GaussianTensorExecution: Forward odd grid sharp
-- statement:
--   Sharpness at every odd dimension, linked to the actual executed impulse.
--
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L324-L329). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L324-L329 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.forward_odd_grid_sharp (q : Nat) :
    ¬ ∃ w : GInt, piIter (2*q+1) w =
      scale ((2 : Int)^q)
        (get (2*q+1) (forward (2*q+1) (lastImpulse (2*q+1))) (firstPath (2*q+1))) := by sorry
