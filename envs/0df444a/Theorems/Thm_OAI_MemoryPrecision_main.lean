-- Prove2me | Theorems.Thm_OAI_MemoryPrecision_main
-- name    : OAI.MemoryPrecision.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:56.405282+00:00
-- url     : https://prove2.me/theorems/6519f316-d12e-41d5-af86-03d810599ec0
-- statement:
--   The theorem states that a conjunction of ten assertions holds, the first eight being previously defined propositions and the last two being explicit bounds on how well a finite-memory learner can recover an unknown unit vector. (1) Gram estimate: for a finite measure μ on R^d supported in a ball of radius R and satisfying the ball bound μ(B(x,r)) ≤ H r^β with β > m+p-2, one gets flat-neighborhood bounds for affine subspaces of dimension j ≤ p-2, finiteness of integrals of dist(s,L)^(-m), almost sure linear independence of difference vectors, and an integral bound on the inverse Gram determinant factor, together with a constant C^d control of these quantities when d ≥ 16, p = d/8 and (d-1)/2 ≤ β ≤ d/2. (2) Such a μ has a nonnegative measurable density F, relative to the Gaussian-matrix-and-label reference measure, for the law of (rows, inner products with the signal), vanishing off the projected ellipsoid and having L^p norm at most an explicit scale. (3) The projection law is bounded by that scale times the (1-1/p)-power of reference measure, and is absolutely continuous, with the same bound for completed measures and integrals of [0,1]-valued test functions over the ellipsoid. (4) If additionally μ is absolutely continuous with respect to the uniform sphere measure, Gaussian regularizations of the density converge in L^1 and the L^p bound persists. (5) An explicit pointwise density exists with a radial-mixture representation, a full-rank formula, a uniqueness property and the L^p bound. (6) A coefficient-step bound shows that mixing sphere-ball-bounded functions with weights summing to at most 1 over N states multiplies the ball constant H by at most C^d N^(1/(d/8)). (7) A source-ellipsoid bound gives an exponentially small bound on success probability and chord success for admissible policies on the uniform sphere. (8) An analogous block bound holds for functions on the cube [-1/2,1/2]^(d/2) embedded into the sphere. (9) There exist D ≥ e, d₀ ≥ 16 and c > 0 such that for d ≥ d₀, M ≤ d², T arbitrary and 0 < ε ≤ 1/10, every kernel family K from a probability space (Ω,ρ) to memory-M, T-step policies that is model-admissible (admissible for every probability prior on the sphere) satisfies, against the cube prior, Success ≤ min(1, D^((d/2)(⌈T/((d/2)/4)⌉+1)) ε^((d/2)/4)); moreover, if for every signal on the sphere the expected indicator that the policy's output lies within angle ε of the signal is at least 2/3 under Gaussian observations, then T ≥ c d log(1/ε). (10) There exist C > 0 and d₀ > 0 such that for d ≥ d₀, all M and T, and 0 < ε ≤ 1/10, every policy family admissible for the uniform sphere prior has angle-ε success probability at most min(1, (2ε exp(C(1+M/d²)⌈T/((d-1)/8)⌉))^((d-1)/2)). The theorem is stated with sorry, not a verified proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MemoryPrecision.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MemoryPrecision.lean; bytes 40195..42396
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MemoryPrecision

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry

open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section

universe u v

namespace MemoryPrecision

theorem main :
  AmbientGramStatement ∧
  FiniteDensityStatement ∧
  MeasurableTestStatement ∧
  JointL1Statement ∧
  PointwiseDensityStatement ∧
  CoefficientStepStatement ∧
  Kernel.SourceEllipsoidStatement.{u} ∧
  CubeBlockStatement ∧
  (∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
    ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.ModelAdmissible.{u} K ρ →
      MemoryPrecision.Kernel.Policy.Success K ρ
        (MemoryPrecision.Kernel.CubePrior (MemoryPrecision.Kernel.cubePrior_dimension hd₀ hd)) ε ≤
          min 1 (ENNReal.ofReal
            (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) ∧
      ((∀ signal : MemoryPrecision.Kernel.Sphere d,
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
        (@OfNat.ofNat ℝ≥0∞ 3
          (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
          (∫⁻ observation,
            MemoryPrecision.Kernel.Policy.experiment K
              (MemoryPrecision.Kernel.Policy.angleTest ε) (signal, observation)
            ∂ρ.prod (MemoryPrecision.Kernel.RowLaw d T))) →
        c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ))) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
    ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
      MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
        ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)))) := by
  sorry

end MemoryPrecision
end
end OAI
