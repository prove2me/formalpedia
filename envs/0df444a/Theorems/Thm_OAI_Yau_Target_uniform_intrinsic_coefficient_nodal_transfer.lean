-- Prove2me | Theorems.Thm_OAI_Yau_Target_uniform_intrinsic_coefficient_nodal_transfer
-- name    : OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:04.621931+00:00
-- url     : https://prove2.me/theorems/8e4d631a-3b2f-4826-a4b7-be3ac6c00459
-- title:
--   OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer` of [lean/OAI/Geometry/NodalSets/Hausdorff/IntrinsicUniformNodal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Hausdorff/IntrinsicUniformNodal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Set MeasureTheory Yau.Jets`, `open scoped ContDiff NNReal ENNReal RealInnerProductSpace`):
--
--   ```lean
--   lemma uniform_intrinsic_coefficient_nodal_transfer
--       (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
--       (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)}
--       (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
--       ∃ C : ℝ≥0, 0 < C ∧
--         ∀ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
--           (hs : ∀ x v w, A x v w = A x w v)
--           (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
--           (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x),
--           (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
--             a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) →
--           (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
--             A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2) →
--           (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
--           ∀ (u : Manifold5 → ℝ) (Z : Set (_root_.OAI.Yau.Jets.Coord × ℝ)), Z ⊆ K →
--             (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
--             Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
--               nodalMeasure (intrinsicWeightedMetric A hA hs hp rho hr hrp) u
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SphereCotangent` and `OAI.Yau.Target.sphereCovectorRestriction` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.productChartDomain` and `OAI.Yau.Target.productChartInverse` (definitions bundle `OAIQ237Ny003` of this split); `OAI.Yau.Target.intrinsicWeightedMetric` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base`, `OAI.Yau.Target.Manifold5` and `OAI.Yau.Target.nodalMeasure` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proofs of `OAI.Yau.Target.sphere_reference_literal_nodal_persistence` and `OAI.Yau.Target.uniform_small_correction_nodal_transfer` of this split import it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Hausdorff/IntrinsicUniformNodal.lean (declaration OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
open Manifold Set MeasureTheory Yau.Jets
open scoped ContDiff NNReal ENNReal RealInnerProductSpace
noncomputable section

lemma uniform_intrinsic_coefficient_nodal_transfer
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
    (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (_root_.OAI.Yau.Jets.Coord × ℝ)}
    (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
        (hs : ∀ x v w, A x v w = A x w v)
        (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
        (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x),
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) →
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2) →
        (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
        ∀ (u : Manifold5 → ℝ) (Z : Set (_root_.OAI.Yau.Jets.Coord × ℝ)), Z ⊆ K →
          (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
          Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
            nodalMeasure (intrinsicWeightedMetric A hA hs hp rho hr hrp) u := by
  sorry

end
end Yau.Target

end OAI
end
