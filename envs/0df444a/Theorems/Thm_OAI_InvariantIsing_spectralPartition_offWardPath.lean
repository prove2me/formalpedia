-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spectralPartition_offWardPath
-- name    : OAI.InvariantIsing.spectralPartition_offWardPath
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:43:27.044216+00:00
-- url     : https://prove2.me/theorems/82385b2a-88b0-4a84-90eb-20df94dc7543
-- title:
--   OAI.InvariantIsing.spectralPartition_offWardPath: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spectralPartition_offWardPath` of [lean/OAI/Probability/InvariantIsing/Spectral/SpectralWardPaths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Spectral/SpectralWardPaths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`):
--
--   ```lean
--    theorem spectralPartition_offWardPath {m : ℕ}
--       {Q : ProbabilityMeasure (SpectralArray (m + 1))}
--       (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
--       (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
--       (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
--       (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
--       (hE : ∀ e : ℕ → ℕ, Function.Injective e →
--         (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
--       (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
--       (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
--       (ρ eig : Fin m → ℝ) (a b : Fin m)
--       (hward : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
--         spectralOffWardResidual Q ρ eig a b Φ = 0) :
--       ∃ f g : ℝ → ℝ, LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
--         (∀ r, f r ∈ Icc (0 : ℝ) 1) ∧ (∀ r, g r ∈ Icc (0 : ℝ) 1) ∧
--         (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
--           (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j)) ∧
--         (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
--           (x (i,j) b.castSucc : ℝ) = g (spectralSpinArray x i j)) ∧
--         (∀ᵐ s ∂pathMeasure, offWardPath (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
--           (fun u => f (spectralSpinQuantilePath Q hP hn u))
--           (fun u => g (spectralSpinQuantilePath Q hP hn u)) s = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry` and `OAI.InvariantIsing.spectralSpinArray` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.offWardPath` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.permuteSpectralArray` and `OAI.InvariantIsing.spectralOffWardResidual` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.spectralSpinQuantilePath` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.HasEntryGhirlandaGuerra` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.pathMeasure` and `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.spectralCanonicalWard_pair` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Spectral/SpectralWardPaths.lean (declaration OAI.InvariantIsing.spectralPartition_offWardPath)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

 theorem spectralPartition_offWardPath {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (a b : Fin m)
    (hward : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0) :
    ∃ f g : ℝ → ℝ, LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      (∀ r, f r ∈ Icc (0 : ℝ) 1) ∧ (∀ r, g r ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j)) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) b.castSucc : ℝ) = g (spectralSpinArray x i j)) ∧
      (∀ᵐ s ∂pathMeasure, offWardPath (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
        (fun u => f (spectralSpinQuantilePath Q hP hn u))
        (fun u => g (spectralSpinQuantilePath Q hP hn u)) s = 0) := by
  sorry

end InvariantIsing

end

end OAI
end
