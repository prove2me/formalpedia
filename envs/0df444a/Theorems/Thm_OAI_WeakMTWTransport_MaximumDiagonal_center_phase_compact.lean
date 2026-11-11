-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_center_phase_compact
-- name    : OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:00.293202+00:00
-- url     : https://prove2.me/theorems/c803d189-d9f6-44fd-a024-5d9400a8bd42
-- title:
--   OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumPhaseCompact.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumPhaseCompact.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma MaximumDiagonal.center_phase_compact {J:MaximumJensenFamily hmtw hv ho F a c N}
--       {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
--       (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
--       (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
--       (he:riemannianExp a q=c)
--       (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
--         (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
--       {C U:ℝ} (hC:0 ≤ C) (hU:0 ≤ U)
--       (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
--       (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
--       ∃g:Model n →L[ℝ] ℝ,∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
--         ∃σ:ℕ → ℕ,StrictMono σ ∧
--         Tendsto (fun i=>fderiv ℝ
--           (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c)
--           ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 g) ∧
--         Tendsto (fun i=>fderiv ℝ
--           (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
--           ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.hopfLax`, `OAI.WeakMTWTransport.subgradientGraph` and `OAI.WeakMTWTransport.ChartFixedPrefixLimit` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedDatum` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.MaximumFamily`, `OAI.WeakMTWTransport.chartCenterEnvelope` and `OAI.WeakMTWTransport.MaximumRow` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.continuous_modifiedDatum` (definitions bundle `OAIQ232A011` of this split); `OAI.WeakMTWTransport.JensenSamplesAt` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex` and `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph` (definitions bundle `OAIQ232A030` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumPhaseCompact.lean (declaration OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact)

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
section MaximumPhaseCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance maximumPhaseDualGroup_r23fd41_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseDualSpace_r23fd41_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearGroup_r23fd41_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearSpace_r23fd41_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.center_phase_compact {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C U:ℝ} (hC:0 ≤ C) (hU:0 ≤ U)
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃g:Model n →L[ℝ] ℝ,∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      ∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun i=>fderiv ℝ
        (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c)
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 g) ∧
      Tendsto (fun i=>fderiv ℝ
        (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B) := by
  sorry

end MaximumPhaseCompact
end WeakMTWTransport

end
end

end OAI
end
