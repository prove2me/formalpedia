-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_isOpen_unit
-- name    : GlobalTheory.CompanionTheory.SW.MassTest.isOpen_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:53.562099+00:00
-- url     : https://prove2.me/theorems/f980a8d2-5b4f-4691-90dd-abb7d6e68347
-- title:
--   Mass Test: is Open unit
-- statement:
--   The Mass Test construction uses the is Open unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L72-L83

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.CompanionTheory.SW.MassTest.isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 2) (Fin 2) E) :
    IsOpen {X : Fin 1 → Fin 2 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by sorry
