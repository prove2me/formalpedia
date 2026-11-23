-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_alpha_in_range
-- name    : GroupTheoreticShannonCapacity.Construction.alpha_in_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:44.480598+00:00
-- url     : https://prove2.me/theorems/7751c5a7-e1c7-494a-87e6-880f4a131386
-- title:
--   Construction: alpha in range
-- statement:
--   The Construction construction uses the alpha in range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L342-L410
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L342-L410

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.alpha_in_range (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    (r : ℚ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n) ∈ Set.Icc 0 1 := by sorry
