-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_det_mul_eq_pow_of_mul_eq_smul
-- name    : GroupTheoreticShannonCapacity.Lattice.det_mul_eq_pow_of_mul_eq_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:36.102783+00:00
-- url     : https://prove2.me/theorems/a00358b1-fc1a-461e-9039-7688972ce0a0
-- title:
--   Lattice: det mul eq pow of mul eq smul
-- statement:
--   From AB = pI, we have det(A) * det(B) = p^n
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L241-L249
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L241-L249

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

theorem GroupTheoreticShannonCapacity.Lattice.det_mul_eq_pow_of_mul_eq_smul (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) (hAB : A * B = p • 1) :
    A.det * B.det = (p : ℤ) ^ (Fintype.card (Fin n)) := by sorry
