-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_q_is_pos_nat
-- name    : GroupTheoreticShannonCapacity.MainProofs.q_is_pos_nat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:36:36.000908+00:00
-- url     : https://prove2.me/theorems/43928b8c-2af8-4815-9c1c-8c1c2ba8c757
-- title:
--   Main Proofs: q is pos nat
-- statement:
--   q is a positive integer.
--
--   Proof: By p_q_are_integers, q ∈ ℤ. Positivity follows from:
--   - Numerator s^(n-1)·r + k·b·a^(n-1) ≥ k·b·a^(n-1) > 0
--   - Denominator r + k·b^n > 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L175-L200
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L175-L200

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.q_is_pos_nat (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ q' : ℕ, 0 < q' ∧ (q' : ℚ) = Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by sorry
