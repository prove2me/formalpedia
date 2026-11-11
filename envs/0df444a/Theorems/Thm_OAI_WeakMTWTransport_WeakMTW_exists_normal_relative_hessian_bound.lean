-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_normal_relative_hessian_bound
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:53.787854+00:00
-- url     : https://prove2.me/theorems/9c535826-3b94-424a-b9dd-a739fce2abbb
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound` of [lean/OAI/Analysis/BiholderTransport/LinearAlgebra/NormalRelativeHessianBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/NormalRelativeHessianBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_normal_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
--       {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {a : M}
--       {p : TangentSpace 𝓘(ℝ,Model n) a} (hp : p∈injectivityDomain a)
--       {m : ℝ} (hm : 0 < m) :
--       ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
--         uv∈densityDualClass (metricVolume n) lam cap x0 →
--         ∀ φ : TangentSpace 𝓘(ℝ,Model n) a → ℝ,
--         ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p → uv.1 a=φ 0 →
--         (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp a w)) →
--         (∀ d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d) →
--         ∀ d,fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d≤C*‖d‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix` and `OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/NormalRelativeHessianBound.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound)

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
import Definitions.Def_OAIQ232A017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section NormalRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_normal_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {a : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} (hp : p∈injectivityDomain a)
    {m : ℝ} (hm : 0 < m) :
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : TangentSpace 𝓘(ℝ,Model n) a → ℝ,
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p → uv.1 a=φ 0 →
      (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp a w)) →
      (∀ d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d) →
      ∀ d,fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d≤C*‖d‖^2 := by
  sorry

end NormalRelativeHessianBound
end WeakMTWTransport

end

end

end

end OAI
end
