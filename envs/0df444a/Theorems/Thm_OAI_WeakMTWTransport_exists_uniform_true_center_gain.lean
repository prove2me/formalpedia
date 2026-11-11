-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_true_center_gain
-- name    : OAI.WeakMTWTransport.exists_uniform_true_center_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:56:49.271633+00:00
-- url     : https://prove2.me/theorems/552d688d-ff16-444e-9214-8c04628d8cc8
-- title:
--   OAI.WeakMTWTransport.exists_uniform_true_center_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_uniform_true_center_gain` of [lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterGain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterGain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma exists_uniform_true_center_gain :
--       ∃c>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → ∀x:M,∀q:TangentSpace 𝓘(ℝ,Model n) x,
--       ∀p:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
--         p∈injectivityDomain (riemannianExp x q) → q∈injectivityDomain x →
--         riemannianExp (riemannianExp x q) (l • p)=x →
--         ∀R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
--         DifferentiableAt ℝ R q → R q=0 →
--         (∀ᶠ z in 𝓝 q,riemannianExp (riemannianExp x q) (R z)=riemannianExp x z) →
--         ∀d,c*(1-l)*‖d‖^2 ≤
--           normalHessian (riemannianExp x q) (l • p) (fderiv ℝ R q d) (fderiv ℝ R q d)-
--           l*normalHessian (riemannianExp x q) p (fderiv ℝ R q d) (fderiv ℝ R q d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.normalHessian` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_true_center_jet_gain` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/TrueCenterGain.lean (declaration OAI.WeakMTWTransport.exists_uniform_true_center_gain)

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

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_true_center_gain :
    ∃c>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → ∀x:M,∀q:TangentSpace 𝓘(ℝ,Model n) x,
    ∀p:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      p∈injectivityDomain (riemannianExp x q) → q∈injectivityDomain x →
      riemannianExp (riemannianExp x q) (l • p)=x →
      ∀R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      DifferentiableAt ℝ R q → R q=0 →
      (∀ᶠ z in 𝓝 q,riemannianExp (riemannianExp x q) (R z)=riemannianExp x z) →
      ∀d,c*(1-l)*‖d‖^2 ≤
        normalHessian (riemannianExp x q) (l • p) (fderiv ℝ R q d) (fderiv ℝ R q d)-
        l*normalHessian (riemannianExp x q) p (fderiv ℝ R q d) (fderiv ℝ R q d) := by
  sorry
end WeakMTWTransport

end

end OAI
end
