-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFin_null_of_fibres_null
-- name    : GlobalTheory.CompanionTheory.SW.LocFin.null_of_fibres_null
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:51.773382+00:00
-- url     : https://prove2.me/theorems/88adfa8b-1afa-47a0-8581-88cebcef98c0
-- title:
--   Loc Fin: null of fibres null
-- statement:
--   The Loc Fin construction uses the null of fibres null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresContinuity.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresContinuity.lean#L16-L23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFin

theorem GlobalTheory.CompanionTheory.SW.LocFin.null_of_fibres_null {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) {W : Set V} (hW : MeasurableSet W)
    (h0 : ∀ b, fib b W = 0) : μ (W ∩ U) = 0 := by sorry
