-- Prove2me | Theorems.Thm_GlobalTheory_AdIdem_exists_idem_isUnit
-- name    : GlobalTheory.AdIdem.exists_idem_isUnit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:25.650927+00:00
-- url     : https://prove2.me/theorems/777d1c64-20f6-4801-9265-eee0add2f4eb
-- title:
--   Ad Idem: exists idem is Unit
-- statement:
--   The Ad Idem construction uses the exists idem is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIdempotentIsUnitOneAddOrSubAdele.lean#L72-L76

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

theorem GlobalTheory.AdIdem.exists_idem_isUnit (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F) :
    ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by sorry
