-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_parametric_short_center_pole_limit
-- name    : OAI.WeakMTWTransport.parametric_short_center_pole_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:48:50.4685+00:00
-- url     : https://prove2.me/theorems/c6b20608-9665-41f4-9df5-75fb4a201911
-- title:
--   OAI.WeakMTWTransport.parametric_short_center_pole_limit: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.parametric_short_center_pole_limit` of [lean/OAI/Analysis/BiholderTransport/Regularity/CenterPoleLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/CenterPoleLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma parametric_short_center_pole_limit {a c : M} {ψ : P×Model n → ℝ}
--       {p : P} (L : ℝ≥0)
--       (hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c))
--       {r : Model n} {v s l : ℝ} {φ : ℝ → ℝ} (hs : s≠0)
--       (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
--       (hφ : HasDerivAt φ l v)
--       (heq : (fun w=>ψ (p,w))=fun w=>coordinateScalarSupport c φ
--         (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
--       {pj : ℕ → P} {xj : ℕ → Model n} {tj τj : ℕ → ℝ}
--       {f : ℕ → M → ℝ} {F : ℕ → Model n → ℝ} {aj : ℕ → M}
--       (hp : Tendsto pj atTop (𝓝 p))
--       (hxx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       (ht : Tendsto tj atTop (𝓝 1)) (hτ : Tendsto τj atTop (𝓝 0))
--       (ha : Tendsto aj atTop (𝓝 a)) (hτpos : ∀ᶠ i in atTop,0<τj i)
--       (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
--       (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
--       (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
--       (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
--         (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
--           (parametricShortForward c ψ ((pj i,τj i),xj i)))
--       (herr : Tendsto (fun i=>fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i))+
--         fderiv ℝ (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
--           (parametricShortForward c ψ ((pj i,τj i),xj i))) atTop (𝓝 0))
--       (hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
--         parametricShortForward c ψ ((pj i,τj i),xj i),
--         fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=aj i) :
--       a=riemannianExp c (l • r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.coordinateBackward`, `OAI.WeakMTWTransport.coordinateScalarSupport` and `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.parametricShortForward` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.CenterSequenceData.regular_compact`, `OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact` and `OAI.WeakMTWTransport.exists_actual_center_sequential_gain` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/CenterPoleLimit.lean (declaration OAI.WeakMTWTransport.parametric_short_center_pole_limit)

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
section CenterPoleLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma parametric_short_center_pole_limit {a c : M} {ψ : P×Model n → ℝ}
    {p : P} (L : ℝ≥0)
    (hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c))
    {r : Model n} {v s l : ℝ} {φ : ℝ → ℝ} (hs : s≠0)
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (hφ : HasDerivAt φ l v)
    (heq : (fun w=>ψ (p,w))=fun w=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj τj : ℕ → ℝ}
    {f : ℕ → M → ℝ} {F : ℕ → Model n → ℝ} {aj : ℕ → M}
    (hp : Tendsto pj atTop (𝓝 p))
    (hxx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (ht : Tendsto tj atTop (𝓝 1)) (hτ : Tendsto τj atTop (𝓝 0))
    (ha : Tendsto aj atTop (𝓝 a)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)))
    (herr : Tendsto (fun i=>fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i))+
      fderiv ℝ (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i))) atTop (𝓝 0))
    (hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=aj i) :
    a=riemannianExp c (l • r) := by
  sorry

end CenterPoleLimit
end WeakMTWTransport

end
end

end OAI
end
