-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_unitChoice_of_isArtinianRing_isReduced
-- name    : GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:01.622979+00:00
-- url     : https://prove2.me/theorems/c9a718ef-144f-4e6e-b0cc-e21852b19e07
-- title:
--   SW: unit Choice of is Artinian Ring is Reduced
-- statement:
--   The SW construction uses the unit Choice of is Artinian Ring is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitChoiceOfIsArtinianRingIsReduced.lean#L11-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitChoiceOfIsArtinianRingIsReduced.lean#L11-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitChoiceOfIsArtinianRingIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by sorry
