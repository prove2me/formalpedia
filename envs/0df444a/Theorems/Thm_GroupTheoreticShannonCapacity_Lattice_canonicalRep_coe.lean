-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_canonicalRep_coe
-- name    : GroupTheoreticShannonCapacity.Lattice.canonicalRep_coe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:12.921916+00:00
-- url     : https://prove2.me/theorems/86668f4d-7ef1-49f3-840c-bfcb61e785c4
-- title:
--   Lattice: canonical Rep coe
-- statement:
--   Canonical representative casts back to original
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L122-L127
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L122-L127

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

theorem GroupTheoreticShannonCapacity.Lattice.canonicalRep_coe (p : ℕ) [hp : NeZero p] (z : ZMod p) :
    (canonicalRep p z : ZMod p) = z := by sorry
