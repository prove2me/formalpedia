-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_labeled_projector_joint_integral
-- name    : OAI.InvariantIsing.cavity_labeled_projector_joint_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:22:04.890234+00:00
-- url     : https://prove2.me/theorems/e8e05569-5b2f-43c9-80e8-a7d6f66e4563
-- title:
--   OAI.InvariantIsing.cavity_labeled_projector_joint_integral: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_labeled_projector_joint_integral` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorJointLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorJointLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory`, `open scoped Matrix BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_labeled_projector_joint_integral {N n m d : ℕ}
--       (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
--       (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
--       (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
--       (es : Fin (m*n) ≃ Fin (d+n))
--       (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
--       (l u : Fin m → ℕ)
--       (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
--       (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
--       (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
--       (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
--       (f : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d → ℝ)
--       (hf : Measurable f) :
--       (∫ U, f (cavityCompressionGrams g U,
--         cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
--       ∫ p, f (cavityCompressionGrams g p.1,
--         cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀)) ∂μ.prod ν
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` and `OAI.InvariantIsing.CavityProjectorFrame` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.cavityCompressionGrams` and `OAI.InvariantIsing.cavityConcreteComplement` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.cavityCanonicalProjectorFrame`, `OAI.InvariantIsing.cavityLabeledProjectorAction` and `OAI.InvariantIsing.cavityPhysicalLabeledProjectors` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.Orthogonal` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_tree_pressure_capped_increment` and `OAI.InvariantIsing.restricted_physical_log_average` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityProjectorJointLaw.lean (declaration OAI.InvariantIsing.cavity_labeled_projector_joint_integral)

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_labeled_projector_joint_integral {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d → ℝ)
    (hf : Measurable f) :
    (∫ U, f (cavityCompressionGrams g U,
      cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ p, f (cavityCompressionGrams g p.1,
      cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀)) ∂μ.prod ν := by
  sorry

end InvariantIsing

end

end OAI
end
