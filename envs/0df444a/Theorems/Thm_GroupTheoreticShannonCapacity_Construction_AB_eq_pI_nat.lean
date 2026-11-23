-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI_nat
-- name    : GroupTheoreticShannonCapacity.Construction.AB_eq_pI_nat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:35:07.792909+00:00
-- url     : https://prove2.me/theorems/97cdc67a-f486-432e-be18-10bda430f282
-- title:
--   Construction: AB eq p I nat
-- statement:
--   AB = pI for natural number parameters with k ≥ 1, b ≥ 1, s ≥ 1.
--       This is the main case needed for the application.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1693-L1713
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1693-L1713

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.AB_eq_pI_nat (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) =
    p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) • 1 := by sorry
