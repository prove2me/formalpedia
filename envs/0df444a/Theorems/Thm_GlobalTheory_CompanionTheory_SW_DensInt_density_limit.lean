-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_DensInt_density_limit
-- name    : GlobalTheory.CompanionTheory.SW.DensInt.density_limit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:04:31.50435+00:00
-- url     : https://prove2.me/theorems/13a33bed-792d-4a92-9831-6ca4d9de0287
-- title:
--   Dens Int: density limit
-- statement:
--   The Dens Int construction uses the density limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityIntegral.lean#L25-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityIntegral.lean#L25-L75

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityIntegral
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DensInt

theorem GlobalTheory.CompanionTheory.SW.DensInt.density_limit {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by sorry
