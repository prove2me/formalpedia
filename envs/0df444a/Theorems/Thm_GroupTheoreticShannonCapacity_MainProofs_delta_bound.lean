-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_delta_bound
-- name    : GroupTheoreticShannonCapacity.MainProofs.delta_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:05.212612+00:00
-- url     : https://prove2.me/theorems/b8afa9fc-7a1b-4ac7-a686-7481842a0037
-- title:
--   Main Proofs: delta bound
-- statement:
--   Lemma 4.6 (lem:Delta_bound): Δ bound
--
--   For n,k,b,r,s ∈ ℝ≥0 with n,k,b ≥ 1 and k,r ≤ b and s ≤ b^n:
--   Δ(n,k,b,r,s) ≤ 6b²/n
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L403-L589
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L403-L589

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.delta_bound (n k b r s : ℝ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hkb : k ≤ b)
    (hr_nonneg : 0 ≤ r) (hrb : r ≤ b)
    (hs_nonneg : 0 ≤ s) (hsbn : s ≤ b ^ n) :
    Delta n k b r s ≤ 6 * b^2 / n := by sorry
