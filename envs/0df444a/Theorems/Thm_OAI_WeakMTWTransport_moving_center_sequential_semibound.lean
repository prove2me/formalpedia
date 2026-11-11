-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_moving_center_sequential_semibound
-- name    : OAI.WeakMTWTransport.moving_center_sequential_semibound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:50:09.775473+00:00
-- url     : https://prove2.me/theorems/2cfed61f-5841-441a-8699-67b907c5a82b
-- title:
--   OAI.WeakMTWTransport.moving_center_sequential_semibound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.moving_center_sequential_semibound` of [lean/OAI/Analysis/BiholderTransport/Convexity/MovingCenterSemibound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MovingCenterSemibound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma moving_center_sequential_semibound {a c : M} {ψ : P×Model n → ℝ}
--       {p : P} {x q : Model n} (L : ℝ≥0)
--       (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
--       (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
--       (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source)
--       {pj : ℕ → P} {xj bj qj : ℕ → Model n} {tj τj : ℕ → ℝ} {f : ℕ → M → ℝ}
--       (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
--       (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
--       (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
--       (hτ : Tendsto τj atTop (𝓝 0)) (hτpos : ∀ᶠ i in atTop,0<τj i)
--       (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
--       (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
--       (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
--       (hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
--         parametricShortForward c ψ ((pj i,τj i),xj i))
--       (hjet : ∀ᶠ i in atTop,
--         (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
--           (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
--         DifferentiableAt ℝ (fderiv ℝ
--           (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
--             (movingPrefixChart a c (tj i) (bj i) (qj i)))
--       {ε : ℝ} (hε : 0<ε) :
--       ∀ᶠ i in atTop,∀ d : Model n,
--         inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
--           fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d-
--             ε*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (hopfLax (τj i) (f i)) (bj i) (qj i) d d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.coordinateCenterMatrix` and `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.movingPrefixChart` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.parametricShortForward` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.exists_actual_center_sequential_gain` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/MovingCenterSemibound.lean (declaration OAI.WeakMTWTransport.moving_center_sequential_semibound)

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
import Definitions.Def_OAIQ232A011
import Definitions.Def_OAIQ232A012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MovingCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma moving_center_sequential_semibound {a c : M} {ψ : P×Model n → ℝ}
    {p : P} {x q : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
    (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {pj : ℕ → P} {xj bj qj : ℕ → Model n} {tj τj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    (hτ : Tendsto τj atTop (𝓝 0)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
      parametricShortForward c ψ ((pj i,τj i),xj i))
    (hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
          (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d : Model n,
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
        fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d-
          ε*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (hopfLax (τj i) (f i)) (bj i) (qj i) d d := by
  sorry

end MovingCenterSemibound
end WeakMTWTransport

end
end

end OAI
end
