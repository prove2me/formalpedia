-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_prefixDefect_taylor
-- name    : OAI.WeakMTWTransport.prefixDefect_taylor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:48:41.991924+00:00
-- url     : https://prove2.me/theorems/bfb0e0b0-c695-41ee-b08d-921d99a603df
-- title:
--   OAI.WeakMTWTransport.prefixDefect_taylor: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.prefixDefect_taylor` of [lean/OAI/Analysis/BiholderTransport/Calculus/FiniteTaylor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/FiniteTaylor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma prefixDefect_taylor {x : M} {t : ℝ} (ht : t≠0)
--       {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x) :
--       ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
--         (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
--         HasSecondTaylor (prefixDefect x t p)
--           ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
--         ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
--           B (a,d) (a,d)=hessianValue x (t • p) a/t-2*inner ℝ a d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasSecondTaylor` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.prefixDefect` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.injectivityDomain` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/FiniteTaylor.lean (declaration OAI.WeakMTWTransport.prefixDefect_taylor)

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

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixDefect_taylor {x : M} {t : ℝ} (ht : t≠0)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x) :
    ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
      HasSecondTaylor (prefixDefect x t p)
        ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
      ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
        B (a,d) (a,d)=hessianValue x (t • p) a/t-2*inner ℝ a d := by
  sorry

end WeakMTWTransport

end

end OAI
end
