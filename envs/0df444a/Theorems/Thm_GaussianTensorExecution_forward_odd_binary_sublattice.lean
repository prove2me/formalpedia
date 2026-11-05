-- Prove2me | Theorems.Thm_GaussianTensorExecution_forward_odd_binary_sublattice
-- name    : GaussianTensorExecution.forward_odd_binary_sublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/31a4ae3f-e171-47b6-a153-4b13f6e3923e
-- title:
--   GaussianTensorExecution: Forward odd binary sublattice
-- statement:
--   At odd tensor depth the converted binary numerator carries the exact index-two Gaussian parity constraint, linked to the executed forward cube.
--
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L389-L398). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L389-L398 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.forward_odd_binary_sublattice (p q : Nat) (z : Cube (2*q+1))
    (path : Path (2*q+1)) :
    ∃ w : GInt, piIter (2*p+(2*q+1)) w =
      scale ((2 : Int)^(p+q+1)) (get (2*q+1) (forward (2*q+1) z) path) ∧ PiDvd w := by sorry
