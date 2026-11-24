-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_map_eq_smul
-- name    : GlobalTheory.CompanionTheory.SW.HaarScale.map_eq_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:07:29.208595+00:00
-- url     : https://prove2.me/theorems/f1f2d6f0-afec-4e54-aaff-a080a5c89b22
-- title:
--   Haar Scale: map eq smul
-- statement:
--   The Haar Scale construction uses the map eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L25-L31

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
variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]

theorem GlobalTheory.CompanionTheory.SW.HaarScale.map_eq_smul (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : V → V) (hT : Continuous T)
    (hTi : Continuous Ti) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) :
    ∃ c : ℝ≥0, μ.map T = c • μ := by sorry
