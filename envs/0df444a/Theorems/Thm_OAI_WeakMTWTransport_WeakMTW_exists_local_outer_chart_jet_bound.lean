-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_local_outer_chart_jet_bound
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:27.660226+00:00
-- url     : https://prove2.me/theorems/51017c23-2ff1-49f7-8f77-f53395bea877
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound` of [lean/OAI/Analysis/BiholderTransport/Coordinates/LocalOuterJetBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/LocalOuterJetBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_local_outer_chart_jet_bound
--       (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
--       (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
--       (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
--         injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
--       {m lmax : ℝ} (hm : 0 < m) (hlmax : 0 < lmax) :
--       ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)),
--         N∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a,L) ∧ ∃ C≥0,
--         ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
--         uv∈densityDualClass (metricVolume n) lam cap x0 →
--         ∀ (z : Model n) (c : Model n → ℝ) (l:ℝ),0 < l → l≤lmax →
--         ContDiffAt ℝ 2 c z → (z,l⁻¹ • (-fderiv ℝ c z))∈N →
--         (∀ d:Model n,2*m*l*‖d‖^2≤
--           l*fderiv ℝ (fderiv ℝ (chartCost a
--             (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z d d-
--             fderiv ℝ (fderiv ℝ c) z d d) →
--         ∀ φ:ℝ → ℝ,StrictMono φ →
--         ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
--         HasDerivAt φ l (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
--         iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z))≤0 →
--         ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
--         HasLowerSecondTaylor (fun h => φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h)))+
--           c (z+h)) 0 H → ∀ d,H d d≤C*‖d‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor` and `OAI.WeakMTWTransport.coordinateBackward` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.chartCost` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.chartGradientVector` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/LocalOuterJetBound.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound)

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
section LocalOuterJetBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_outer_chart_jet_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m lmax : ℝ} (hm : 0 < m) (hlmax : 0 < lmax) :
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)),
      N∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a,L) ∧ ∃ C≥0,
      ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (c : Model n → ℝ) (l:ℝ),0 < l → l≤lmax →
      ContDiffAt ℝ 2 c z → (z,l⁻¹ • (-fderiv ℝ c z))∈N →
      (∀ d:Model n,2*m*l*‖d‖^2≤
        l*fderiv ℝ (fderiv ℝ (chartCost a
          (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z d d-
          fderiv ℝ (fderiv ℝ c) z d d) →
      ∀ φ:ℝ → ℝ,StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      HasDerivAt φ l (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z))≤0 →
      ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
      HasLowerSecondTaylor (fun h => φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h)))+
        c (z+h)) 0 H → ∀ d,H d d≤C*‖d‖^2 := by
  sorry

end LocalOuterJetBound
end WeakMTWTransport

end

end

end

end OAI
end
