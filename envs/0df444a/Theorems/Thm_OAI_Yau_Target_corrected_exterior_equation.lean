-- Prove2me | Theorems.Thm_OAI_Yau_Target_corrected_exterior_equation
-- name    : OAI.Yau.Target.corrected_exterior_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:18.919008+00:00
-- url     : https://prove2.me/theorems/9be47641-f921-4c93-bd66-de8534a1f645
-- title:
--   OAI.Yau.Target.corrected_exterior_equation: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.corrected_exterior_equation` of [lean/OAI/Geometry/NodalSets/Elliptic/ExteriorCorrectedEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/ExteriorCorrectedEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Set Filter`, `open scoped ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem corrected_exterior_equation (A : IntrinsicTensor) (rho : Base → ℝ)
--       {K L : Set Base} (hK : IsClosed K) (hL : IsClosed L)
--       (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
--         ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
--         A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
--       (hr : ∀ x ∉ K, rho x = 1) (a b u : Base → ℝ) (n : ℕ)
--       (ha : tsupport a ⊆ L) (hb : tsupport b ⊆ L) (hu : tsupport (u-sphericalSeed n) ⊆ L)
--       (p : Base) (z : BaseModel) (hz : (extChartAt (𝓡 4) p).symm z ∉ K ∪ L) :
--       -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
--         (fun x ↦ rho x+b x) u p z = seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.SphereCotangent`, `OAI.Yau.Target.seedEigenvalue`, `OAI.Yau.Target.sphereCovectorRestriction` and `OAI.Yau.Target.sphericalSeed` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.exteriorCorrectedEquationLocalInst11`, `OAI.Yau.Target.exteriorCorrectedEquationLocalInst9`, `OAI.Yau.Target.intrinsicWeightedChartOperator` and `OAI.Yau.Target.roundTensorPerturbation` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_positive_sphere_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/ExteriorCorrectedEquation.lean (declaration OAI.Yau.Target.corrected_exterior_equation)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance exteriorCorrectedEquationLocalInst1_rb0a114_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst2_rb0a114_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst3_rb0a114_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst4_rb0a114_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst5_rb0a114_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst6_rb0a114_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst7
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst8
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst9
local instance exteriorCorrectedEquationLocalInst10_rb0a114_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst11
local instance exteriorCorrectedEquationLocalInst12_rb0a114_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance exteriorCorrectedEquationLocalInst13_rb0a114_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance exteriorCorrectedEquationLocalInst14_rb0a114_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance exteriorCorrectedEquationLocalInst15_rb0a114_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst16_rb0a114_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
theorem corrected_exterior_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    {K L : Set Base} (hK : IsClosed K) (hL : IsClosed L)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (a b u : Base → ℝ) (n : ℕ)
    (ha : tsupport a ⊆ L) (hb : tsupport b ⊆ L) (hu : tsupport (u-sphericalSeed n) ⊆ L)
    (p : Base) (z : BaseModel) (hz : (extChartAt (𝓡 4) p).symm z ∉ K ∪ L) :
    -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
      (fun x ↦ rho x+b x) u p z = seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm z) := by
  sorry

end
end Yau.Target

end OAI
end
