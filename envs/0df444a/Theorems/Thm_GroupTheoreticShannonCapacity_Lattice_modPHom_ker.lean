-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_ker
-- name    : GroupTheoreticShannonCapacity.Lattice.modPHom_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:39.150156+00:00
-- url     : https://prove2.me/theorems/8250f631-4b64-427f-b35f-c1bbc9bbbde1
-- title:
--   Lattice: mod PHom ker
-- statement:
--   The kernel of modPHom is exactly pℤ^n
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L309-L325
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean#L309-L325

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

theorem GroupTheoreticShannonCapacity.Lattice.modPHom_ker (n : ℕ) (p : ℕ) [NeZero p] :
    (modPHom n p).ker = pZn n p := by sorry
