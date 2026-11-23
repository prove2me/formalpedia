-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_surjective
-- name    : GroupTheoreticShannonCapacity.Lattice.modPHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:28:29.26543+00:00
-- url     : https://prove2.me/theorems/835d13b8-517b-49d5-8415-e9443800750d
-- title:
--   Lattice: mod PHom surjective
-- statement:
--   modPHom is surjective
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L328-L337
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L328-L337

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

theorem GroupTheoreticShannonCapacity.Lattice.modPHom_surjective (n : ℕ) (p : ℕ) [NeZero p] :
    Function.Surjective (modPHom n p) := by sorry
