-- Prove2me | Theorems.Thm_GaussianTensorExecution_forward_even_grid_sharp
-- name    : GaussianTensorExecution.forward_even_grid_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/00fe9b59-e719-429c-9438-b675f7c3ef90
-- title:
--   GaussianTensorExecution: Forward even grid sharp
-- statement:
--   The tensor's actual impulse coordinate cannot fit a one-bit coarser binary grid at positive even dimension.
--
--   Finite tensor forward and inverse execution, exact reconstruction, and binary-grid bounds.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L316-L321). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/GaussianTensorExecution.lean#L316-L321 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis

theorem GaussianTensorExecution.forward_even_grid_sharp (q : Nat) :
    ¬ ∃ w : GInt, piIter (2*(q+1)) w =
      scale ((2 : Int)^q)
        (get (2*(q+1)) (forward (2*(q+1)) (lastImpulse (2*(q+1)))) (firstPath (2*(q+1)))) := by sorry
