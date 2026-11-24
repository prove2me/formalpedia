-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_idempotent_isUnit_one_add_or_sub_adele
-- name    : GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:40.883243+00:00
-- url     : https://prove2.me/theorems/f329d262-5201-4ff9-b19f-c82a5a82d79e
-- title:
--   T: exists idempotent is Unit one add or sub adele
-- statement:
--   The T construction uses the exists idempotent is Unit one add or sub adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdeleStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdeleStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdele
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele : ∀ (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F), ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by sorry
