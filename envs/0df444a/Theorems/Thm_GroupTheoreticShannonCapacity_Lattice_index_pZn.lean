-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_index_pZn
-- name    : GroupTheoreticShannonCapacity.Lattice.index_pZn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:28:25.91295+00:00
-- url     : https://prove2.me/theorems/ea2300f1-0b69-455b-9578-0fc8d089960a
-- title:
--   Lattice: index p Zn
-- statement:
--   The index [ℤ^n : pℤ^n] = p^n
--
--       Proof: The quotient ℤ^n / pℤ^n ≅ (ℤ/pℤ)^n has p^n elements.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L342-L351
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L342-L351

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

theorem GroupTheoreticShannonCapacity.Lattice.index_pZn (n : ℕ) [NeZero n] (p : ℕ) [NeZero p] :
    (pZn n p).index = p ^ n := by sorry
