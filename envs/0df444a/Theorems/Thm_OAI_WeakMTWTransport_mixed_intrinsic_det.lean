-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_mixed_intrinsic_det
-- name    : OAI.WeakMTWTransport.mixed_intrinsic_det
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:57:18.997586+00:00
-- url     : https://prove2.me/theorems/85f13fce-6347-41dd-948b-da86cac6d37d
-- title:
--   OAI.WeakMTWTransport.mixed_intrinsic_det: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.mixed_intrinsic_det` of [lean/OAI/Analysis/BiholderTransport/Regularity/MixedDetIntrinsic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MixedDetIntrinsic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma mixed_intrinsic_det {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
--       (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
--       (hp:p∈injectivityDomain x)
--       (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
--       chartJacobian (n:=n) a x *
--         |(mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
--           (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).det| *
--         (chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p)=1
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.chartJacobian` and `OAI.WeakMTWTransport.expJacobian` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.mixedCostOperator` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MixedDetIntrinsic.lean (declaration OAI.WeakMTWTransport.mixed_intrinsic_det)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MixedDetIntrinsic
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance midFinite_r078d61_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] in
lemma mixed_intrinsic_det {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp:p∈injectivityDomain x)
    (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    chartJacobian (n:=n) a x *
      |(mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
        (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).det| *
      (chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p)=1 := by
  sorry

end MixedDetIntrinsic
end WeakMTWTransport

end
end

end OAI
end
