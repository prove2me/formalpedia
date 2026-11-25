-- Prove2me | Theorems.Thm_GlobalTheory_CohenStructure_isAdicComplete_of_ringEquiv
-- name    : GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:43.751442+00:00
-- url     : https://prove2.me/theorems/c762d027-5ab6-4eb2-9f6d-5657c3a67d6d
-- title:
--   Cohen Structure: is Adic Complete of ring Equiv
-- statement:
--   The Cohen Structure construction uses the is Adic Complete of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CohenStructureFiniteOverNormalCompleteSubring.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CohenStructureFiniteOverNormalCompleteSubring.lean#L28-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDVROfClosedSubringPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSystemOfParametersInsert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.CohenStructure

theorem GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [h : IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by sorry
