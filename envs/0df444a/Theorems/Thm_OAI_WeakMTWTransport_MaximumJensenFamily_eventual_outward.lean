-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_eventual_outward
-- name    : OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:40:53.365515+00:00
-- url     : https://prove2.me/theorems/323249e0-0c74-49e0-ad3a-209984cfc6d3
-- title:
--   OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutward.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutward.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma MaximumJensenFamily.eventual_outward
--       {hmtw:WeakMTW (n:=n) (M:=M)} {u v:M → ℝ}
--       (hu:Continuous u) {hv:Continuous v} (hdual:IsCostDualPair u v)
--       {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
--       {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
--       (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
--       (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
--       (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
--       {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
--       {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
--         (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
--       {A C:ℝ} (hA:0 < A) (hC:C < 0)
--       (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
--         A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
--           C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
--       {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
--       (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
--       (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
--       (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
--       (hosc:∀k,sectionOscillation u v (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D) :
--       ∀ᶠ k in atTop,
--         let b:=graphBaseCoordinate a (F.row k).q.1
--         let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
--         let P:=chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)
--         let si:=fun i=>(v (riemannianExp x (chartFiberInverse a b ((J.first k).pj₀ i)))-α)/D
--         ∃e:TangentSpace 𝓘(ℝ,Model n) x,∃i:Fin (Module.finrank ℝ (Model n)+1),∃d:ℝ,
--           ‖e‖=1 ∧ 0 < inner ℝ P e ∧ a0*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
--           chartFiberInverse a b ((J.first k).pj₀ i)=P+d • e ∧
--           (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ (J.first k).w₀ i ∧
--           (1/4096)*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ (J.first k).w₀ i*d ∧
--           d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
--           Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.chartFiberInverse`, `OAI.WeakMTWTransport.graphBaseCoordinate`, `OAI.WeakMTWTransport.graphVelocityCoordinate`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.sectionOscillation` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOutward.lean (declaration OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward)

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
section MaximumOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.eventual_outward
    {hmtw:WeakMTW (n:=n) (M:=M)} {u v:M → ℝ}
    (hu:Continuous u) {hv:Continuous v} (hdual:IsCostDualPair u v)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation u v (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D) :
    ∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
      let P:=chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp x (chartFiberInverse a b ((J.first k).pj₀ i)))-α)/D
      ∃e:TangentSpace 𝓘(ℝ,Model n) x,∃i:Fin (Module.finrank ℝ (Model n)+1),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ a0*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        chartFiberInverse a b ((J.first k).pj₀ i)=P+d • e ∧
        (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ (J.first k).w₀ i ∧
        (1/4096)*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
        Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) := by
  sorry

end MaximumOutward
end WeakMTWTransport

end
end

end OAI
end
