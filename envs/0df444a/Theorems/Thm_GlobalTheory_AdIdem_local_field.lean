-- Prove2me | Theorems.Thm_GlobalTheory_AdIdem_local_field
-- name    : GlobalTheory.AdIdem.local_field
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:18.10381+00:00
-- url     : https://prove2.me/theorems/6eb07367-18bb-4d7a-bac8-ac218828962a
-- title:
--   Ad Idem: local field
-- statement:
--   The Ad Idem construction uses the local field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L22-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdele
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
open GlobalTheory GlobalTheory.AdIdem

theorem GlobalTheory.AdIdem.local_field {K : Type*} [Field K] (h2 : (1 + 1 : K) ≠ 0) (s : K) :
    ∃ e : K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by sorry
