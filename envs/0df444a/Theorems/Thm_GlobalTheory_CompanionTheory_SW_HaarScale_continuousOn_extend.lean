-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_continuousOn_extend
-- name    : GlobalTheory.CompanionTheory.SW.HaarScale.continuousOn_extend
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:24.147644+00:00
-- url     : https://prove2.me/theorems/e8e6b04a-945d-4cf3-94aa-03e318c57c07
-- title:
--   Haar Scale: continuous On extend
-- statement:
--   The Haar Scale construction uses the continuous On extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L109-L115

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
variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.HaarScale.continuousOn_extend (A : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} → ℝ≥0)
    (hA : Continuous A) [∀ g : Matrix (Fin n) (Fin n) K, Decidable (IsUnit g.det)] :
    ContinuousOn (fun g : Matrix (Fin n) (Fin n) K => if h : IsUnit g.det then A ⟨g, h⟩ else 0)
      {g | IsUnit g.det} := by sorry
