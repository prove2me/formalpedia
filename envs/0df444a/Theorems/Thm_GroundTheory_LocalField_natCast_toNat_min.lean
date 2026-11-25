-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCast_toNat_min
-- name    : GroundTheory.LocalField.natCast_toNat_min
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:35.960585+00:00
-- url     : https://prove2.me/theorems/70db0b65-5f8c-4d45-be81-8958a4e09ee8
-- title:
--   Local Field: nat Cast to Nat min
-- statement:
--   The Local Field construction uses the nat Cast to Nat min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L21-L22

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

theorem GroundTheory.LocalField.natCast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℕ∞) = min n m := by sorry
