-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_haar_comap
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.haar_comap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:31.155979+00:00
-- url     : https://prove2.me/theorems/e998679e-46a4-40a5-8437-712a0149e816
-- title:
--   Haar Coord: haar comap
-- statement:
--   The Haar Coord construction uses the haar comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L11-L21

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.haar_comap {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (f : G → H) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hf : IsHomeomorph f) (μ : Measure H) [μ.IsAddHaarMeasure] :
    (Measure.comap f μ).IsAddHaarMeasure := by sorry
