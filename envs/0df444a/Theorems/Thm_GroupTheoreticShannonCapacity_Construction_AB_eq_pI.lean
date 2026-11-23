-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI
-- name    : GroupTheoreticShannonCapacity.Construction.AB_eq_pI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:35:24.532492+00:00
-- url     : https://prove2.me/theorems/946760ea-e926-49c0-86e1-b601f759e51b
-- title:
--   Construction: AB eq p I
-- statement:
--   AB = pI for natural number parameters with k ≥ 1, b ≥ 1.
--       The s = 0 case is handled using a polynomial identity argument:
--       both sides are polynomial in s, agree for all s ≥ 1, hence are identical.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1747-L2159
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1747-L2159

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.AB_eq_pI (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) =
    p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) • 1 := by sorry
