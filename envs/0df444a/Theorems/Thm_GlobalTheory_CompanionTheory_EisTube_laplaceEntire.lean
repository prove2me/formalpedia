-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_laplaceEntire
-- name    : GlobalTheory.CompanionTheory.EisTube.laplaceEntire
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:22.482832+00:00
-- url     : https://prove2.me/theorems/61fb7412-af8c-4455-b4d6-31b8db8442b1
-- title:
--   Eis Tube: laplace Entire
-- statement:
--   The Eis Tube construction uses the laplace Entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L158-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L158-L243

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.laplaceEntire (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P]
    [FirstCountableTopology P] (h : P → ℝ) (hh : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ nhds p, BddAbove (h '' U))
    (ψ : P → (ι → ℝ) → ℂ) (hm : ∀ p, MeasureTheory.AEStronglyMeasurable (ψ p))
    (hc : ∀ t, Continuous (fun p => ψ p t))
    (hv : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t,
      ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) :
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) := by sorry
