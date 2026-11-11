-- Prove2me | Theorems.Thm_OAI_Yau_Target_uniform_small_correction_nodal_transfer
-- name    : OAI.Yau.Target.uniform_small_correction_nodal_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:16.136847+00:00
-- url     : https://prove2.me/theorems/94021342-628d-4fff-b18e-1f56609bb84e
-- title:
--   OAI.Yau.Target.uniform_small_correction_nodal_transfer: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.uniform_small_correction_nodal_transfer` of [lean/OAI/Geometry/NodalSets/Hausdorff/PerturbedNodalTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Hausdorff/PerturbedNodalTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Yau.Jets Set MeasureTheory`, `open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal`):
--
--   ```lean
--   theorem uniform_small_correction_nodal_transfer (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
--       (hs : ∀ x v w, A x v w = A x w v)
--       (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
--       (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
--       {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H) :
--       ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
--         ∀ (alpha beta : Base → ℝ)
--           (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation alpha x))
--           (hnewSym : ∀ x v w, (A x+roundTensorPerturbation alpha x) v w =
--             (A x+roundTensorPerturbation alpha x) w v)
--           (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v)
--           (hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+beta x))
--           (hrnewPos : ∀ x, 0 < rho x+beta x),
--           (∀ x, |alpha x| ≤ eta) → (∀ x, |beta x| ≤ eta) →
--           ∀ (u : _root_.OAI.Yau.Jets.Coord → ℝ) (ug : Base → ℝ) (U : Set _root_.OAI.Yau.Jets.Coord), U ⊆ H →
--             (∀ x, ug (seedSphereFromCoord x) = u x) →
--             Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : _root_.OAI.Yau.Jets.Coord × ℝ | u z.1 = 0}) ≤
--               (C:ℝ≥0∞)^4 * nodalMeasure
--                 (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation alpha x) hnew hnewSym hnewPos
--                   (fun x ↦ rho x+beta x) hrnew hrnewPos) (circleLift ug)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SphereCotangent` and `OAI.Yau.Target.circleLift` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.seedSphereFromCoord` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicWeightedMetric`, `OAI.Yau.Target.perturbedNodalTransferLocalInst11`, `OAI.Yau.Target.perturbedNodalTransferLocalInst9` and `OAI.Yau.Target.roundTensorPerturbation` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` and `OAI.Yau.Target.nodalMeasure` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_global_sphere_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Hausdorff/PerturbedNodalTransfer.lean (declaration OAI.Yau.Target.uniform_small_correction_nodal_transfer)

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
import Mathlib.MeasureTheory.Measure.Hausdorff
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

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance perturbedNodalTransferLocalInst1_rbbeda3_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst2_rbbeda3_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst3_rbbeda3_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst4_rbbeda3_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst5_rbbeda3_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst6_rbbeda3_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst7
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst8
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst9
local instance perturbedNodalTransferLocalInst10_rbbeda3_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst11
local instance perturbedNodalTransferLocalInst12_rbbeda3_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance perturbedNodalTransferLocalInst13_rbbeda3_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance perturbedNodalTransferLocalInst14_rbbeda3_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance perturbedNodalTransferLocalInst15_rbbeda3_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst16_rbbeda3_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
theorem uniform_small_correction_nodal_transfer (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (alpha beta : Base → ℝ)
        (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation alpha x))
        (hnewSym : ∀ x v w, (A x+roundTensorPerturbation alpha x) v w =
          (A x+roundTensorPerturbation alpha x) w v)
        (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v)
        (hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+beta x))
        (hrnewPos : ∀ x, 0 < rho x+beta x),
        (∀ x, |alpha x| ≤ eta) → (∀ x, |beta x| ≤ eta) →
        ∀ (u : _root_.OAI.Yau.Jets.Coord → ℝ) (ug : Base → ℝ) (U : Set _root_.OAI.Yau.Jets.Coord), U ⊆ H →
          (∀ x, ug (seedSphereFromCoord x) = u x) →
          Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : _root_.OAI.Yau.Jets.Coord × ℝ | u z.1 = 0}) ≤
            (C:ℝ≥0∞)^4 * nodalMeasure
              (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation alpha x) hnew hnewSym hnewPos
                (fun x ↦ rho x+beta x) hrnew hrnewPos) (circleLift ug) := by
  sorry

end
end Yau.Target

end OAI
end
