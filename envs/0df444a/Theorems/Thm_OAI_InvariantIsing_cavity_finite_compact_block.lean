-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_finite_compact_block
-- name    : OAI.InvariantIsing.cavity_finite_compact_block
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:19:39.579008+00:00
-- url     : https://prove2.me/theorems/c9720b5d-e73c-4212-b9ec-88f54a223e01
-- title:
--   OAI.InvariantIsing.cavity_finite_compact_block: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_finite_compact_block` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCascadeBlock.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCascadeBlock.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Set`, `open scoped Matrix BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma cavity_finite_compact_block {m n r : ℕ}
--       (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
--       (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
--       (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (σ : ℕ → LabeledLeaf n) :
--       cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
--         (cavityCanonicalLabel rho lam hrho hsum p)
--         (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1
--           (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ)))) =
--         cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.cavityCanonicalLabel`, `OAI.InvariantIsing.cavityFiniteLevel` and `OAI.InvariantIsing.cavitySynchronizedBlock` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCanonicalDiagonal` and `OAI.InvariantIsing.cavityFiniteReplicaSpectralBlock` (definitions bundle `OAIQ258003` of this split); `OAI.IsingPerceptron.JointArray`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.arrayBlock`, `OAI.IsingPerceptron.cascadeScalarArray`, `OAI.IsingPerceptron.compactScalarArray`, `OAI.IsingPerceptron.diagonalPatch` and `OAI.IsingPerceptron.spinArray` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.OverlapPath` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_finite_cascade_block_average`, `OAI.InvariantIsing.cavity_haar_restricted_gibbs_regularized_match` and `OAI.InvariantIsing.cavity_strict_recalculated_gaussian_error` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityFiniteCascadeBlock.lean (declaration OAI.InvariantIsing.cavity_finite_compact_block)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_finite_compact_block {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (σ : ℕ → LabeledLeaf n) :
    cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p)
      (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1
        (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ)))) =
      cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i) := by
  sorry

end InvariantIsing

end

end OAI
end
