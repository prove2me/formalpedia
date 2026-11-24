-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_KUnits_continuousOn_ringInverse
-- name    : GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:33.582353+00:00
-- url     : https://prove2.me/theorems/6b5f7edd-bed6-4c45-84c0-b3c697a94e1b
-- title:
--   KUnits: continuous On ring Inverse
-- statement:
--   The KUnits construction uses the continuous On ring Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitsOpenEmbeddingLocalTensor.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitsOpenEmbeddingLocalTensor.lean#L10-L20

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KUnits

theorem GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (h : IsOpenEmbedding (Units.val : Rˣ → R)) :
    ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by sorry
