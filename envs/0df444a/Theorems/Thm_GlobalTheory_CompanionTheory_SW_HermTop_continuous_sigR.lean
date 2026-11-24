-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_continuous_sigR
-- name    : GlobalTheory.CompanionTheory.SW.HermTop.continuous_sigR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:00.141505+00:00
-- url     : https://prove2.me/theorems/7442f90f-0fbb-4e97-a9f7-19109dfaa21e
-- title:
--   Herm Top: continuous sig R
-- statement:
--   The Herm Top construction uses the continuous sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L55-L59

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.SW.HermTop.continuous_sigR [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by sorry
