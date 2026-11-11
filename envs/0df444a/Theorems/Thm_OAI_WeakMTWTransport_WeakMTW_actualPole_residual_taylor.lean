-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_residual_taylor
-- name    : OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:51:59.763804+00:00
-- url     : https://prove2.me/theorems/ee517af0-e253-413b-a533-c8984d7468f7
-- title:
--   OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor` of [lean/OAI/Analysis/BiholderTransport/Duality/ActualLowerJet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Duality/ActualLowerJet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.actualPole_residual_taylor (hmtw : WeakMTW (n := n) (M := M))
--       {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
--       {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
--       {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
--       {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
--       {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
--       (ha : HasFDerivAt a R p) (ha0 : a p=0)
--       (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
--         hopfPole (n := n) t u (riemannianExp x (t • q))) :
--       HasSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
--         hopfLax t u (riemannianExp x (t • (p+d)))-t*(‖p+d‖^2/2))
--         0 (-((innerSL ℝ).comp R))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasSecondTaylor`, `OAI.WeakMTWTransport.IsCostDualPair` and `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hopfPole` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Duality/ActualLowerJet.lean (declaration OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor)

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

lemma WeakMTW.actualPole_residual_taylor (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • (p+d)))-t*(‖p+d‖^2/2))
      0 (-((innerSL ℝ).comp R)) := by
  sorry

end WeakMTWTransport

end

end OAI
end
