-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_exists_continuous_scale
-- name    : GlobalTheory.CompanionTheory.SW.HaarScale.exists_continuous_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:42.022228+00:00
-- url     : https://prove2.me/theorems/80f21d54-406f-4607-81be-ced800c8c617
-- title:
--   Haar Scale: exists continuous scale
-- statement:
--   The Haar Scale construction uses the exists continuous scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L33-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L33-L70

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

theorem GlobalTheory.CompanionTheory.SW.HaarScale.exists_continuous_scale (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : P → V → V)
    (hT : Continuous (Function.uncurry T)) (hTi : Continuous (Function.uncurry Ti))
    (hadd : ∀ p x y, T p (x + y) = T p x + T p y)
    (hl : ∀ p x, Ti p (T p x) = x) (hr : ∀ p x, T p (Ti p x) = x) :
    ∃ A : P → ℝ≥0, Continuous A ∧ ∀ p, μ.map (T p) = A p • μ := by sorry
