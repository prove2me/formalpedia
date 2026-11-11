-- Prove2me | Theorems.Thm_OAI_Yau_Target_seed_envelope_coordinate_patch
-- name    : OAI.Yau.Target.seed_envelope_coordinate_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:32.152294+00:00
-- url     : https://prove2.me/theorems/c0f1fccc-fd85-4b66-a0fc-087c1920a85c
-- title:
--   OAI.Yau.Target.seed_envelope_coordinate_patch: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.seed_envelope_coordinate_patch` of [lean/OAI/Geometry/NodalSets/Elliptic/SeedEnvelopePatch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/SeedEnvelopePatch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Set Metric`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem seed_envelope_coordinate_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
--       IsCompact (closedBall (0 : BaseModel) r) ∧ IsCompact (seedCoordinateCube a) ∧
--       seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
--       (∀ y ∈ closedBall (0 : BaseModel) r,
--         seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
--       ∀ c : BaseModel → CoefficientPoint BaseModel,
--         (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
--         (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
--           α ≠ 0 → 0 < α ((c y).1 α)) →
--         (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
--         (∀ y ∈ closedBall (0 : BaseModel) r,
--           dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
--         ∀ y ∈ closedBall (0 : BaseModel) r,
--           let g := coefficientMetricValue ∘ c
--           let p := localMetricGradient g seedRealChart y
--           let H := localMetricHessian g seedRealChart y
--           (∀ v : BaseModel, v ≠ 0 → 0 < g y v v) ∧ p ≠ 0 ∧
--           ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
--             0 < H p p + (g y p p+4)*H t t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.coefficientMetricValue`, `OAI.Yau.Geometry.localMetricGradient` and `OAI.Yau.Geometry.localMetricHessian` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.SeedAmbient`, `OAI.Yau.Target.seedChartAmbient`, `OAI.Yau.Target.seedCoordinateCube`, `OAI.Yau.Target.seedImagChart`, `OAI.Yau.Target.seedLogDomain` and `OAI.Yau.Target.seedRealChart` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.roundCoefficientJet` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_noncritical_placed_data` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/SeedEnvelopePatch.lean (declaration OAI.Yau.Target.seed_envelope_coordinate_patch)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OAIQ237Ny002

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

theorem seed_envelope_coordinate_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧ IsCompact (seedCoordinateCube a) ∧
    seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
      (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
        α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        let g := coefficientMetricValue ∘ c
        let p := localMetricGradient g seedRealChart y
        let H := localMetricHessian g seedRealChart y
        (∀ v : BaseModel, v ≠ 0 → 0 < g y v v) ∧ p ≠ 0 ∧
        ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
          0 < H p p + (g y p p+4)*H t t := by
  sorry

end
end Yau.Target

end OAI
end
