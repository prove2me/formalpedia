-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_selected_pole_compact
-- name    : OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:41.020608+00:00
-- url     : https://prove2.me/theorems/16febf92-5f84-4b5c-861a-32e527cb403c
-- title:
--   OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSelectionCompact.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSelectionCompact.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma MaximumJensenFamily.selected_pole_compact
--       {hmtw:WeakMTW (n:=n) (M:=M)} {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
--       {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
--       {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
--       {F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo}
--       {a c:M} {N:Set (Model n)}
--       (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
--       (hd:IsCostDualPair (uv.1:M → ℝ) uv.2)
--       (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
--       (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
--       (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
--       {q:Model n} {β:ℝ} (hβ:Tendsto F.b atTop (𝓝 β))
--       (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
--       {A C:ℝ} (hA:0 < A) (hC:C < 0)
--       (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
--         A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
--         C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
--       {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
--       (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
--       (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
--       (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
--       (hosc:∀k,sectionOscillation uv.1 uv.2 (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D)
--       (hmono:∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s)))
--       (hmargin:∀s:ℝ,-2*eta ≤ s → s ≤ 1-eta →
--         Bo s ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) →
--         1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
--         iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0) :
--       ∃σ:ℕ → ℕ,StrictMono σ ∧
--       ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
--       ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
--       ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃CL:ℝ,0 ≤ CL ∧
--       ∃i:Fin (Module.finrank ℝ (Model n)+1),
--         Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
--         Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
--         Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) ∧
--         (∀ᶠ k in atTop,∀d,(J.first (σ k)).L d d ≤ CL*‖d‖^2) ∧
--         (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈minimizingVectors a) ∧
--         (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧
--         (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ m i ∧
--         -2*eta ≤ (uv.2 (riemannianExp a (r i))-α)/D ∧
--         (uv.2 (riemannianExp a (r i))-α)/D ≤ 1-eta ∧
--         Bo ((uv.2 (riemannianExp a (r i))-α)/D) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) ∧
--         ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
--           (show TangentSpace 𝓘(ℝ,Model n) a from r i)=
--             (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
--           0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
--           a0*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
--           ‖show TangentSpace 𝓘(ℝ,Model n) a from r i‖^2-
--             ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*a0))*D
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.minimizingVectors`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.modifiedScalar` (definitions bundle `OAIQ232A004` of this split); `OAI.WeakMTWTransport.MaximumFamily` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.sectionOscillation` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.MaximumJensenFamily` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumSelectionCompact.lean (declaration OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact)

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
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSelectionCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.selected_pole_compact
    {hmtw:WeakMTW (n:=n) (M:=M)} {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
    {F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)}
    (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
    (hd:IsCostDualPair (uv.1:M → ℝ) uv.2)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {q:Model n} {β:ℝ} (hβ:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
      C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation uv.1 uv.2 (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D)
    (hmono:∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s)))
    (hmargin:∀s:ℝ,-2*eta ≤ s → s ≤ 1-eta →
      Bo s ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) →
      1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
      iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
    ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃CL:ℝ,0 ≤ CL ∧
    ∃i:Fin (Module.finrank ℝ (Model n)+1),
      Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
      Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
      Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) ∧
      (∀ᶠ k in atTop,∀d,(J.first (σ k)).L d d ≤ CL*‖d‖^2) ∧
      (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈minimizingVectors a) ∧
      (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧
      (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ m i ∧
      -2*eta ≤ (uv.2 (riemannianExp a (r i))-α)/D ∧
      (uv.2 (riemannianExp a (r i))-α)/D ≤ 1-eta ∧
      Bo ((uv.2 (riemannianExp a (r i))-α)/D) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) ∧
      ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
        (show TangentSpace 𝓘(ℝ,Model n) a from r i)=
          (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
        0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
        a0*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
        ‖show TangentSpace 𝓘(ℝ,Model n) a from r i‖^2-
          ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*a0))*D := by
  sorry

end MaximumSelectionCompact
end WeakMTWTransport

end
end

end OAI
end
