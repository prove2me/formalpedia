-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conjT_one
-- name    : GlobalTheory.CompanionTheory.SW.HaarScale.conjT_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:12.176827+00:00
-- url     : https://prove2.me/theorems/1ece1d96-dbd1-40a9-87af-3e06af056e9e
-- title:
--   Haar Scale: conj T one
-- statement:
--   The Haar Scale construction uses the conj T one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L153-L158

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.HaarScale.conjT_one (σ : E →ₐ[F] E) {n : ℕ} :
    conjT R σ (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by sorry
