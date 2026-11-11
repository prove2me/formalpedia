-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_modified_active_lower_jet_nonneg
-- name    : OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:53:05.503597+00:00
-- url     : https://prove2.me/theorems/12f9a81f-f8cb-4345-b948-577809118ef1
-- title:
--   OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg` of [lean/OAI/Analysis/BiholderTransport/Regularity/NonnegativeTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/NonnegativeTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.modified_active_lower_jet_nonneg (hmtw : WeakMTW (n := n) (M := M))
--       {v : M → ℝ} (hv : Continuous v)
--       {t s : ℝ} (ht : 0<t) (hts : t < s) (hs1 : s<1) {x:M}
--       {ι : Type*} [Fintype ι]
--       (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
--       (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι) (hi : 0<w i)
--       (hmin : ∀ j,pj j∈minimizingVectors x)
--       (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
--       (hleft : ∀ j,s • pj j∈injectivityDomain x)
--       (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
--         injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
--       {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
--       {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
--       (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
--       (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
--         hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
--       HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
--         v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
--         (w i • ((innerSL ℝ).comp R))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor`, `OAI.WeakMTWTransport.cTransform`, `OAI.WeakMTWTransport.contactGap` and `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hopfPole` and `OAI.WeakMTWTransport.sprayFlow` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/NonnegativeTransfer.lean (declaration OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg)

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
import Definitions.Def_OAIQ232A013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.modified_active_lower_jet_nonneg (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι) (hi : 0<w i)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  sorry

end WeakMTWTransport

end

end OAI
end
