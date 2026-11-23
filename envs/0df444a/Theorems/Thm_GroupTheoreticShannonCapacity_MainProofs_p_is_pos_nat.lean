-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_p_is_pos_nat
-- name    : GroupTheoreticShannonCapacity.MainProofs.p_is_pos_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:24.345566+00:00
-- url     : https://prove2.me/theorems/bc8dd49b-3dd4-4471-a394-90205018dc90
-- title:
--   Main Proofs: p is pos nat
-- statement:
--   p is a positive integer.
--
--   Proof: By p_q_are_integers, p ∈ ℤ. Positivity follows from:
--   - Numerator s^n·r + k·a^n ≥ k·a^n > 0 (since k ≥ 1 and a > 0)
--   - Denominator r + k·b^n > 0 (since k, b ≥ 1)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L144-L168
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L144-L168

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.p_is_pos_nat (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ p' : ℕ, 0 < p' ∧ (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) := by sorry
