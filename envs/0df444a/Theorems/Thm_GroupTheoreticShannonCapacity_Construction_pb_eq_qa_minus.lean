-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_pb_eq_qa_minus
-- name    : GroupTheoreticShannonCapacity.Construction.pb_eq_qa_minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:31.897572+00:00
-- url     : https://prove2.me/theorems/f52e8014-cce5-46cd-a7bc-e974d157ad27
-- title:
--   Construction: pb eq qa minus
-- statement:
--   (ii) pb = qa - rs^{n-1} (Lemma 3.8(ii), lem:pqdef)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L147-L187
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L147-L187

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.pb_eq_qa_minus (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hd : r + k * b ^ n ≠ 0) :
    p n k b r s * b = q n k b r s * (a n k b r s) - r * s^(n-1) := by sorry
