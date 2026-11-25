-- Prove2me | Theorems.Thm_GroundTheory_LocalField_cast_toNat_min
-- name    : GroundTheory.LocalField.cast_toNat_min
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:27.043108+00:00
-- url     : https://prove2.me/theorems/7a30832b-fe48-4063-b4ea-25f58201d894
-- title:
--   Local Field: cast to Nat min
-- statement:
--   The Local Field construction uses the cast to Nat min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel

theorem GroundTheory.LocalField.cast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℝ) = enatMin n m := by sorry
