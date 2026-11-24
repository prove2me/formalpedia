-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_exists_compactOpen
-- name    : GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:22:01.594328+00:00
-- url     : https://prove2.me/theorems/7bf6f2b0-484d-47e5-9fce-9b02b2649513
-- title:
--   Mass Test: exists compact Open
-- statement:
--   The Mass Test construction uses the exists compact Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L39-L48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MassTest

theorem GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W]
    [TotallyDisconnectedSpace W] [MeasurableSpace W] (ν : Measure W) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set W} (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ A : Set W, IsCompact A ∧ IsOpen A ∧ A ⊆ U ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by sorry
