-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_gramR_ratTup_apply
-- name    : GlobalTheory.CompanionTheory.SW.MassTest.gramR_ratTup_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:25.000864+00:00
-- url     : https://prove2.me/theorems/ec4f9ddd-bab4-4052-b5d1-b7bff9ccd7fa
-- title:
--   Mass Test: gram R rat Tup apply
-- statement:
--   The Mass Test construction uses the gram R rat Tup apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L54-L57

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.CompanionTheory.SW.MassTest.gramR_ratTup_apply (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) (a c : Fin n) :
    gramR R σ J (ratTup R Y) a c = inclR R (gramE σ J Y a c) := by sorry
