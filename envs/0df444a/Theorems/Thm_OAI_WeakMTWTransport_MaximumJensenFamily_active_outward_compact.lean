-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_active_outward_compact
-- name    : OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:54.143196+00:00
-- url     : https://prove2.me/theorems/e0c6cf2d-0c1f-4ac9-a90c-64f6ce1db980
-- title:
--   OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutwardCompact.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutwardCompact.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma MaximumJensenFamily.active_outward_compact
--       {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
--       {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
--       {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
--       {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
--       {q:Model n} {β μ ν κ eta U:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
--       (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
--         (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
--       (hμ:0 < μ) (hν:0 < ν) (hκ:0 < κ) (hD:0 < D)
--       (hsel:∀ᶠ k in atTop,
--         let b:=graphBaseCoordinate a (F.row k).q.1
--         let A:=chartFiberInverse a b
--         let P:=A (graphVelocityCoordinate a (F.row k).q.1)
--         let si:=fun i=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
--           (A ((J.first k).pj₀ i)))-α)/D
--         ∃i:Fin (Module.finrank ℝ (Model n)+1),
--         ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b),∃d:ℝ,
--           ‖e‖=1 ∧ 0 < inner ℝ P e ∧ κ*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
--           A ((J.first k).pj₀ i)=P+d • e ∧ μ ≤ (J.first k).w₀ i ∧
--           ν*D/(inner ℝ P e) ≤ (J.first k).w₀ i*d ∧
--           d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧ Bo (si i) ≤ U) :
--       ∃σ:ℕ → ℕ,StrictMono σ ∧
--         ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
--         ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
--         ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
--           Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
--           Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
--           (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
--             activeLogs (modifiedDatum v α D β Bo) a) ∧
--           (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧ μ ≤ m i₀ ∧
--           (∀ᶠ k in atTop,μ ≤ (J.first (σ k)).w₀ i₀) ∧
--           -2*eta ≤ (v (riemannianExp a (r i₀))-α)/D ∧
--           (v (riemannianExp a (r i₀))-α)/D ≤ 1-eta ∧
--           Bo ((v (riemannianExp a (r i₀))-α)/D) ≤ U ∧
--           ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
--             (show TangentSpace 𝓘(ℝ,Model n) a from r i₀)=
--               (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
--             0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
--             κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
--             ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m i₀*d ∧
--             d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
--             ‖show TangentSpace 𝓘(ℝ,Model n) a from r i₀‖^2-
--               ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.activeLogs`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.graphBaseCoordinate`, `OAI.WeakMTWTransport.graphVelocityCoordinate`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutwardCompact.lean (declaration OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact)

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
import Definitions.Def_OAIQ232A030

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
section MaximumOutwardCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.active_outward_compact
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} {β μ ν κ eta U:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (hμ:0 < μ) (hν:0 < ν) (hκ:0 < κ) (hD:0 < D)
    (hsel:∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let A:=chartFiberInverse a b
      let P:=A (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        (A ((J.first k).pj₀ i)))-α)/D
      ∃i:Fin (Module.finrank ℝ (Model n)+1),
      ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ κ*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        A ((J.first k).pj₀ i)=P+d • e ∧ μ ≤ (J.first k).w₀ i ∧
        ν*D/(inner ℝ P e) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧ Bo (si i) ≤ U) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
      ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
      ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
      ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
        Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
        Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
        (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
          activeLogs (modifiedDatum v α D β Bo) a) ∧
        (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧ μ ≤ m i₀ ∧
        (∀ᶠ k in atTop,μ ≤ (J.first (σ k)).w₀ i₀) ∧
        -2*eta ≤ (v (riemannianExp a (r i₀))-α)/D ∧
        (v (riemannianExp a (r i₀))-α)/D ≤ 1-eta ∧
        Bo ((v (riemannianExp a (r i₀))-α)/D) ≤ U ∧
        ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
          (show TangentSpace 𝓘(ℝ,Model n) a from r i₀)=
            (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
          0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
          κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
          ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m i₀*d ∧
          d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
          ‖show TangentSpace 𝓘(ℝ,Model n) a from r i₀‖^2-
            ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D := by
  sorry

end MaximumOutwardCompact
end WeakMTWTransport

end
end

end OAI
end
