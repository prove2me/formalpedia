-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_incl_injective
-- name    : GlobalTheory.AdLat.UnitRoot.incl_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:57.186932+00:00
-- url     : https://prove2.me/theorems/d09d0f54-4532-46a4-a375-bd899c9fb843
-- title:
--   Unit Root: incl injective
-- statement:
--   The Unit Root construction uses the incl injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L59-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.AdLat.UnitRoot.incl_injective : Function.Injective (incl F) := by sorry
