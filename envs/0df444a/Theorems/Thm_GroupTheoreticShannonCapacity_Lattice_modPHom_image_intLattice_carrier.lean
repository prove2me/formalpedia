-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_image_intLattice_carrier
-- name    : GroupTheoreticShannonCapacity.Lattice.modPHom_image_intLattice_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:28:45.260848+00:00
-- url     : https://prove2.me/theorems/b59b3419-be8c-4687-9165-b1e4698a5243
-- title:
--   Lattice: mod PHom image int Lattice carrier
-- statement:
--   The carrier of the image of intLatticeOfMatrix under modPHom equals latticeQuotient
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L406-L430
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L406-L430

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.Lattice.modPHom_image_intLattice_carrier (n : ℕ) (p : ℕ) [NeZero p] (A : Matrix (Fin n) (Fin n) ℤ) :
    (AddSubgroup.map (modPHom n p) (intLatticeOfMatrix n A) : Set (Fin n → ZMod p)) =
      latticeQuotient n p A := by sorry
