-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_distMod_eq_abs_canonicalRep
-- name    : GroupTheoreticShannonCapacity.Lattice.distMod_eq_abs_canonicalRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:28:10.839917+00:00
-- url     : https://prove2.me/theorems/e6299d52-c30a-47ed-9ec5-0ff05d166434
-- title:
--   Lattice: dist Mod eq abs canonical Rep
-- statement:
--   distMod equals the absolute value of the canonical representative
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L106-L119
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L106-L119

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

theorem GroupTheoreticShannonCapacity.Lattice.distMod_eq_abs_canonicalRep (p : ℕ) [hp : NeZero p] (z : ZMod p) :
    distMod p z 0 = Int.natAbs (canonicalRep p z) := by sorry
