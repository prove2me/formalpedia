-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_pZn_le_intLattice
-- name    : GroupTheoreticShannonCapacity.Lattice.pZn_le_intLattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:22.716022+00:00
-- url     : https://prove2.me/theorems/49c2a7ba-eed8-430f-8633-9ab2c8dc9a05
-- title:
--   Lattice: p Zn le int Lattice
-- statement:
--   pℤ^n is contained in L(A) when AB = pI
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L282-L300
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L282-L300

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

theorem GroupTheoreticShannonCapacity.Lattice.pZn_le_intLattice (n : ℕ) [NeZero n] (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    (hAB : A * B = p • 1) : pZn n p ≤ intLatticeOfMatrix n A := by sorry
