-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_density_of_pairing
-- name    : GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_of_pairing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:26.00657+00:00
-- url     : https://prove2.me/theorems/0988dc25-fc3b-416b-b48f-8e08024a8bf9
-- title:
--   Dens: density of pairing
-- statement:
--   The Dens construction uses the density of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L202-L207

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {T : Type} [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousSMul ℝ T] [T2Space T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

theorem GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_of_pairing (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (m : Measure T) [IsFiniteMeasure m] (ν : Measure T) [ν.IsAddHaarMeasure]
    (hi : Integrable (fun u => ∫ y, Complex.exp (2 * π * I * ((B u y : ℝ) : ℂ)) ∂m) ν) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ Y, MeasurableSet Y → m Y ≤ C * ν Y := by sorry
