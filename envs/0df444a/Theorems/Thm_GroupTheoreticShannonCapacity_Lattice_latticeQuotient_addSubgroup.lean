-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_latticeQuotient_addSubgroup
-- name    : GroupTheoreticShannonCapacity.Lattice.latticeQuotient_addSubgroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:04.85831+00:00
-- url     : https://prove2.me/theorems/3ab22631-c3b9-4390-93aa-d7ffd6b24b36
-- title:
--   Lattice: lattice Quotient add Subgroup
-- statement:
--   The quotient set forms an additive subgroup
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L71-L99
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L71-L99

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

theorem GroupTheoreticShannonCapacity.Lattice.latticeQuotient_addSubgroup (n : ℕ) (p : ℕ) [NeZero p] (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ H : AddSubgroup (Fin n → ZMod p),
      (H : Set (Fin n → ZMod p)) = latticeQuotient n p A := by sorry
