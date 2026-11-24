-- Prove2me | Theorems.Thm_GlobalTheory_AdIdem_infinite_part
-- name    : GlobalTheory.AdIdem.infinite_part
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:31.759717+00:00
-- url     : https://prove2.me/theorems/5dea3b21-9bc0-46cd-ba1a-401fdc5a1760
-- title:
--   Ad Idem: infinite part
-- statement:
--   The Ad Idem construction uses the infinite part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L62-L70

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

theorem GlobalTheory.AdIdem.infinite_part (K : Type*) [Field K] [CharZero K] (s : InfiniteAdeleRing K) :
    ∃ e : InfiniteAdeleRing K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by sorry
