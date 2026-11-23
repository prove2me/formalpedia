-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_numer_ne_zero_nat
-- name    : GroupTheoreticShannonCapacity.Construction.numer_ne_zero_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:26.513101+00:00
-- url     : https://prove2.me/theorems/569e28ea-e2d4-4a71-9744-ebdc9ac0f54e
-- title:
--   Construction: numer ne zero nat
-- statement:
--   For natural number parameters with k ≥ 1, b ≥ 1, s ≥ 1, the numerator is nonzero.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1687-L1689
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1687-L1689

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.numer_ne_zero_nat (n k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    (s : ℤ) ^ n * (r : ℤ) + (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n ≠ 0 := by sorry
