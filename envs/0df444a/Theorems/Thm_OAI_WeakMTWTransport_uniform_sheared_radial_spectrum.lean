-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_uniform_sheared_radial_spectrum
-- name    : OAI.WeakMTWTransport.uniform_sheared_radial_spectrum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:59:35.108238+00:00
-- url     : https://prove2.me/theorems/893a7b3c-d593-495f-9523-73523a237762
-- title:
--   OAI.WeakMTWTransport.uniform_sheared_radial_spectrum: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.uniform_sheared_radial_spectrum` of [lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ShearedSpectrum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ShearedSpectrum.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle ContinuousLinearMap`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma uniform_sheared_radial_spectrum {a B : ℝ} (ha : 0<a) (hB : 0<B)
--       (haB : a*B≤1/2) :
--       ∃ l u b : ℝ, 0<l ∧ 0<u ∧ 0<b ∧
--         ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
--         0 < inner ℝ p q → ‖q‖^2/inner ℝ p q≤B →
--         (∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x) →
--         ∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (-a) 1,
--         ∃ hF : (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric,
--         ∀ i : Fin (Module.finrank ℝ (Model n)),
--         l*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)-b*δ ≤
--           hF.eigenvalues rfl i ∧
--         hF.eigenvalues rfl i ≤
--           u*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)+b*δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.endpointExpDifferential` and `OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_12` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.shearedRadialOperator` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/ShearedSpectrum.lean (declaration OAI.WeakMTWTransport.uniform_sheared_radial_spectrum)

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

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearedSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_12
lemma uniform_sheared_radial_spectrum {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (haB : a*B≤1/2) :
    ∃ l u b : ℝ, 0<l ∧ 0<u ∧ 0<b ∧
      ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q≤B →
      (∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x) →
      ∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (-a) 1,
      ∃ hF : (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric,
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      l*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)-b*δ ≤
        hF.eigenvalues rfl i ∧
      hF.eigenvalues rfl i ≤
        u*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)+b*δ := by
  sorry
end ShearedSpectrum
end WeakMTWTransport

end

end

end

end OAI
end
