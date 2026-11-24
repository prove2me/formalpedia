-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_nhdsNE_Fv
-- name    : GlobalTheory.CompanionTheory.SW.NullV.nhdsNE_Fv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:20:55.441536+00:00
-- url     : https://prove2.me/theorems/8fb08273-4d8e-4952-a1ba-6d60e9c501b2
-- title:
--   Null V: nhds NE Fv
-- statement:
--   The Null V construction uses the nhds NE Fv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L148-L151

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
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
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.CompanionTheory.SW.NullV.nhdsNE_Fv : (𝓝[≠] (0 : Fv F v)).NeBot := by sorry
