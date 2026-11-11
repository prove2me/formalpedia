-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_true_center_jet_gain
-- name    : OAI.WeakMTWTransport.exists_true_center_jet_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:56:51.19962+00:00
-- url     : https://prove2.me/theorems/e078231e-8e58-49d8-8b15-c182368a9e3c
-- title:
--   OAI.WeakMTWTransport.exists_true_center_jet_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_true_center_jet_gain` of [lean/OAI/Analysis/BiholderTransport/Calculus/TrueCenterJet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/TrueCenterJet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma exists_true_center_jet_gain : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
--       ∀l∈U,0<l → l<1 → ∀(u:M → ℝ) (a c:M) (φ:ℝ → ℝ),
--       ∀J:TrueCenterJet (n:=n) u a c φ l,
--       ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
--         (bilinearOperator V).det=(chartFiberInverse a J.b).toLinearMap.normDet^2*l^n*
--           (expJacobian J.shortRay.1 J.shortRay.2)^2*(normalHessianOperator J.y J.p+J.A).det ∧
--         ∀d,V d d+δ*(1-l)*frameMetric a J.b d d+
--           (J.curvature/l^2)*(frameMetric a J.b J.q d)^2≤J.matrix d d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.chartFiberInverse` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.bilinearOperator` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.expJacobian` and `OAI.WeakMTWTransport.frameMetric` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.TrueCenterJet`, `OAI.WeakMTWTransport.normalHessianOperator`, `OAI.WeakMTWTransport.TrueCenterJet.curvature`, `OAI.WeakMTWTransport.TrueCenterJet.matrix` and `OAI.WeakMTWTransport.TrueCenterJet.shortRay` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_true_center_limit` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/TrueCenterJet.lean (declaration OAI.WeakMTWTransport.exists_true_center_jet_gain)

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
section TrueCenterJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance trueCenterJetFinite_r392b7f_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_true_center_jet_gain : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀l∈U,0<l → l<1 → ∀(u:M → ℝ) (a c:M) (φ:ℝ → ℝ),
    ∀J:TrueCenterJet (n:=n) u a c φ l,
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a J.b).toLinearMap.normDet^2*l^n*
        (expJacobian J.shortRay.1 J.shortRay.2)^2*(normalHessianOperator J.y J.p+J.A).det ∧
      ∀d,V d d+δ*(1-l)*frameMetric a J.b d d+
        (J.curvature/l^2)*(frameMetric a J.b J.q d)^2≤J.matrix d d := by
  sorry

end TrueCenterJet
end WeakMTWTransport

end
end

end OAI
end
