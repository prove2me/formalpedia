-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_tup_continuousSMul
-- name    : GlobalTheory.CompanionTheory.SW.ScaleCont.tup_continuousSMul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:07.083882+00:00
-- url     : https://prove2.me/theorems/a1f404d0-a695-43d5-bad4-0b54795e40c3
-- title:
--   Scale Cont: tup continuous SMul
-- statement:
--   The Scale Cont construction uses the tup continuous SMul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L97-L108

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ScaleCont
variable {K : Type} [CommRing K] {n M : ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K]

theorem GlobalTheory.CompanionTheory.SW.ScaleCont.tup_continuousSMul :
    @ContinuousSMul (GL (Fin n) K) (Fin n → Fin M → K) (tupAction (K := K)).toSMul _ _ := by sorry
