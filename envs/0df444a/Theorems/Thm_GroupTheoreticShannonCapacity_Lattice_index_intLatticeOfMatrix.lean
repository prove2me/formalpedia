-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_index_intLatticeOfMatrix
-- name    : GroupTheoreticShannonCapacity.Lattice.index_intLatticeOfMatrix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:33.63514+00:00
-- url     : https://prove2.me/theorems/7d656adb-5594-4e4d-8c6a-31eaccf9751c
-- title:
--   Lattice: index int Lattice Of Matrix
-- statement:
--   The index [ℤ^n : L(A)] = |det(A)| when det(A) ≠ 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L365-L403
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L365-L403

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

theorem GroupTheoreticShannonCapacity.Lattice.index_intLatticeOfMatrix (n : ℕ) [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hdetA : A.det ≠ 0) :
    (intLatticeOfMatrix n A).index = A.det.natAbs := by sorry
