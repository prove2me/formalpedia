-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_density_transport
-- name    : GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_transport
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:56.849999+00:00
-- url     : https://prove2.me/theorems/1e7b390f-b693-4f3e-b6ee-d1d8457decdc
-- title:
--   Dens: density transport
-- statement:
--   The Dens construction uses the density transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L218-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L218-L265

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
  {X H : Type} [MeasurableSpace X] [MeasurableSpace H]

theorem GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_transport (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (μ : Measure X) (ν : Measure H) (Ψ : H ≃ᵐ T) (hν : (ν.map Ψ).IsAddHaarMeasure)
    (q : X → H) (hq : Measurable q) (P : X → ℝ≥0) (hP : Measurable P)
    (hfin : ∫⁻ x, P x ∂μ ≠ ⊤) (S : Set X) (hS : ∀ x ∈ S, 1 ≤ P x)
    (hi : Integrable (fun b => ∫ x, (P x : ℂ) * Complex.exp (2 * π * I * ((B (Ψ b) (Ψ (q x)) : ℝ) : ℂ)) ∂μ) ν) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ Y, MeasurableSet Y → μ (S ∩ q ⁻¹' Y) ≤ C * ν Y := by sorry
