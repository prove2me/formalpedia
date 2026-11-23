-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_sR_sub_aI_isUnit
-- name    : GroupTheoreticShannonCapacity.Construction.sR_sub_aI_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:12.174443+00:00
-- url     : https://prove2.me/theorems/a4d8dd97-d605-40d5-b489-c9ec093f5cfb
-- title:
--   Construction: s R sub a I is Unit
-- statement:
--   sR - aI is invertible when s^n*r + k*a^n ≠ 0 (for natural number parameters)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1211-L1238
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1211-L1238

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.sR_sub_aI_isUnit (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hn_num : (s : ℤ) ^ n * (r : ℤ) +
      (k : ℤ) * (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) ^ n ≠ 0) :
    IsUnit ((s : ℝ) • MAlpha.Rα n ((r : ℝ) / (k : ℝ)) -
      (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℝ) • 1) := by sorry
