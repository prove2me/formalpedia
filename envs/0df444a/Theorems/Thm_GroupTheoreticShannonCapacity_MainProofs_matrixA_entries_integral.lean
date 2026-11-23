-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_matrixA_entries_integral
-- name    : GroupTheoreticShannonCapacity.MainProofs.matrixA_entries_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:35:32.939808+00:00
-- url     : https://prove2.me/theorems/f5cbdeed-c54b-4c04-9112-512f5977b731
-- title:
--   Main Proofs: matrix A entries integral
-- statement:
--   The entries of matrixA are integers.
--
--   Proof: matrixA = q·I + X where:
--   - q is an integer (by p_q_are_integers)
--   - X entries are products of integers k, b, r, s, a
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L38-L68
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L38-L68

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.matrixA_entries_integral (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ A' : Matrix (Fin n) (Fin n) ℤ,
      matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ) := by sorry
