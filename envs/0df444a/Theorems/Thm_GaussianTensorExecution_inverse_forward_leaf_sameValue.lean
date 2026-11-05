-- Prove2me | Theorems.Thm_GaussianTensorExecution_inverse_forward_leaf_sameValue
-- name    : GaussianTensorExecution.inverse_forward_leaf_sameValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/ac499f47-db06-478d-99f0-b1245d95ecc2
-- title:
--   GaussianTensorExecution: Inverse forward leaf same Value
-- statement:
--   Every returned coordinate restores its exact input value when the two raw tensor calls charge their actual 2D denominator units.
--
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L241-L245). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L241-L245 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.inverse_forward_leaf_sameValue (n e : Nat) (z : Cube n) (p : Path n) :
    SameValue ⟨get n (inverse n (forward n z)) p,e+2*n⟩ ⟨get n z p,e⟩ := by sorry
