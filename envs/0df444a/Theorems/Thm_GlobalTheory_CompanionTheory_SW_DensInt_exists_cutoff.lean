-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_DensInt_exists_cutoff
-- name    : GlobalTheory.CompanionTheory.SW.DensInt.exists_cutoff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:04:17.221196+00:00
-- url     : https://prove2.me/theorems/fe4f16a0-9d87-47af-a3c2-09708f80e6a2
-- title:
--   Dens Int: exists cutoff
-- statement:
--   The Dens Int construction uses the exists cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityIntegral.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityIntegral.lean#L12-L23

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_exists_cutoff

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

theorem GlobalTheory.CompanionTheory.SW.DensInt.exists_cutoff (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by sorry
