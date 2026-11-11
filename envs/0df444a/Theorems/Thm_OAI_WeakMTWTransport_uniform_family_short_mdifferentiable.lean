-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_uniform_family_short_mdifferentiable
-- name    : OAI.WeakMTWTransport.uniform_family_short_mdifferentiable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:45:15.668526+00:00
-- url     : https://prove2.me/theorems/f1bb72ed-891a-4bf7-860c-df3115c4b034
-- title:
--   OAI.WeakMTWTransport.uniform_family_short_mdifferentiable: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.uniform_family_short_mdifferentiable` of [lean/OAI/Analysis/BiholderTransport/Regularity/FamilyGlobal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/FamilyGlobal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Metric Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma uniform_family_short_mdifferentiable {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
--       {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
--       {Lφ : ℝ≥0} (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) :
--       ∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
--         ∀ τ:ℝ,0<τ → τ<δ →
--         MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (fun y=>Φ (p,cTransform u y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.cTransform` and `OAI.WeakMTWTransport.hopfLax` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.Model` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.class_power` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/FamilyGlobal.lean (declaration OAI.WeakMTWTransport.uniform_family_short_mdifferentiable)

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
import Definitions.Def_OAIQ232A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section FamilyGlobal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_short_mdifferentiable {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    {Lφ : ℝ≥0} (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) :
    ∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ τ:ℝ,0<τ → τ<δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (fun y=>Φ (p,cTransform u y))) := by
  sorry
end FamilyGlobal
end WeakMTWTransport

end
end

end OAI
end
