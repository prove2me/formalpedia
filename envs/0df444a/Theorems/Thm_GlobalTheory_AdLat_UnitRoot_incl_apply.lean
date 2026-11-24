-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_incl_apply
-- name    : GlobalTheory.AdLat.UnitRoot.incl_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:50.761873+00:00
-- url     : https://prove2.me/theorems/6d36fdf2-f709-4fcf-a9cd-38d5c87dbd21
-- title:
--   Unit Root: incl apply
-- statement:
--   The Unit Root construction uses the incl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L57-L57

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

theorem GlobalTheory.AdLat.UnitRoot.incl_apply (a : IntAd F) (v) : incl F a v = a v := by sorry
