-- Prove2me | Theorems.Thm_GlobalTheory_CohenStructure_isAdicComplete_mvPowerSeries
-- name    : GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:45.670805+00:00
-- url     : https://prove2.me/theorems/62435837-113a-4b79-91ca-aea0a833f36a
-- title:
--   Cohen Structure: is Adic Complete mv Power Series
-- statement:
--   The Cohen Structure construction uses the is Adic Complete mv Power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CohenStructureFiniteOverNormalCompleteSubring.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CohenStructureFiniteOverNormalCompleteSubring.lean#L34-L41

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

theorem GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by sorry
