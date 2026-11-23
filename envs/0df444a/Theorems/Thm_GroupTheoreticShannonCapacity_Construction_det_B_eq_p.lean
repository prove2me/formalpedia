-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_det_B_eq_p
-- name    : GroupTheoreticShannonCapacity.Construction.det_B_eq_p
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:35:32.653863+00:00
-- url     : https://prove2.me/theorems/6380c1ff-324c-41ae-8eba-d6f77553bf7f
-- title:
--   Construction: det B eq p
-- statement:
--   The Construction construction uses the det B eq p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L2237-L2259
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L2237-L2259

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.det_B_eq_p (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (matrixB n k b r s).det = p n k b r s := by sorry
