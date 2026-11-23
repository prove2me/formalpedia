-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_intLatticeOfMatrix_toSubmodule
-- name    : GroupTheoreticShannonCapacity.Lattice.intLatticeOfMatrix_toSubmodule
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:33.000865+00:00
-- url     : https://prove2.me/theorems/59f18381-2af2-4c31-8a03-5f46b2b1402b
-- title:
--   Lattice: int Lattice Of Matrix to Submodule
-- statement:
--   The intLatticeOfMatrix as a submodule equals the range of mulVecLin
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L354-L362
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L354-L362

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

theorem GroupTheoreticShannonCapacity.Lattice.intLatticeOfMatrix_toSubmodule (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    (intLatticeOfMatrix n A).toIntSubmodule = LinearMap.range A.mulVecLin := by sorry
