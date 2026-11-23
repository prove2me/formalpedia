-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_distMod_eq_canonicalRep_diff
-- name    : GroupTheoreticShannonCapacity.Lattice.distMod_eq_canonicalRep_diff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:14.781561+00:00
-- url     : https://prove2.me/theorems/94574a23-7591-4011-a4e3-cc4885525c26
-- title:
--   Lattice: dist Mod eq canonical Rep diff
-- statement:
--   For lattice quotient differences, distMod equals |canonicalRep|
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L147-L150
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L147-L150

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

theorem GroupTheoreticShannonCapacity.Lattice.distMod_eq_canonicalRep_diff (p : ℕ) [hp : NeZero p] (u v : ZMod p) :
    distMod p u v = Int.natAbs (canonicalRep p (u - v)) := by sorry
