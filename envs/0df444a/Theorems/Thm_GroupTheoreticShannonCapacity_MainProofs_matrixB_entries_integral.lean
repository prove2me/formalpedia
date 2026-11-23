-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_matrixB_entries_integral
-- name    : GroupTheoreticShannonCapacity.MainProofs.matrixB_entries_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:20.108803+00:00
-- url     : https://prove2.me/theorems/ecf2956b-5bb8-4623-a1bc-c4fc5d874779
-- title:
--   Main Proofs: matrix B entries integral
-- statement:
--   The entries of matrixB are integers.
--
--   Proof: matrixB = ((a-r)/b)·I + Y where:
--   - (a-r)/b = k·b^(n-1) + s is an integer (since a = k·b^n + s·b + r)
--   - Y entries are products of integers k, b, r
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L75-L114
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L75-L114

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.matrixB_entries_integral (n k b r s : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) :
    ∃ B' : Matrix (Fin n) (Fin n) ℤ,
      matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ) := by sorry
