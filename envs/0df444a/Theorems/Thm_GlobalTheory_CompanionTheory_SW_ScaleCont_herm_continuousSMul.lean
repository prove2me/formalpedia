-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_herm_continuousSMul
-- name    : GlobalTheory.CompanionTheory.SW.ScaleCont.herm_continuousSMul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:10.348095+00:00
-- url     : https://prove2.me/theorems/407bf2b6-4325-465a-8a96-cedfa5d8ef3c
-- title:
--   Scale Cont: herm continuous SMul
-- statement:
--   The Scale Cont construction uses the herm continuous SMul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L110-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L110-L125

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

theorem GlobalTheory.CompanionTheory.SW.ScaleCont.herm_continuousSMul (s : K →+* K) (hs : Continuous s)
    (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    @ContinuousSMul (GL (Fin n) K) H (hermAction s H hmem).toSMul _ _ := by sorry
