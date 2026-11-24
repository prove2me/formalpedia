-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_measurableEmbedding_hermScal
-- name    : GlobalTheory.CompanionTheory.SW.ArchFibre.measurableEmbedding_hermScal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:18.580733+00:00
-- url     : https://prove2.me/theorems/ec25d241-7342-4ef1-8f3a-eb162ded61fe
-- title:
--   Arch Fibre: measurable Embedding herm Scal
-- statement:
--   The Arch Fibre construction uses the measurable Embedding herm Scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanBinaryGramDensity.lean#L132-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanBinaryGramDensity.lean#L132-L143

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
variable [MeasurableSpace R] [BorelSpace R]

theorem GlobalTheory.CompanionTheory.SW.ArchFibre.measurableEmbedding_hermScal (h : IsCMExt F E σ) [IsTopologicalRing R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    MeasurableEmbedding (hermScal R σ (F := F) (E := E)) := by sorry
