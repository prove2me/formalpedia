-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_movingFixedJoinMiddle_strict_crossing
-- name    : OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:53:14.0473+00:00
-- url     : https://prove2.me/theorems/3d64057d-72ff-4900-886d-bcb4571d2326
-- title:
--   OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing` of [lean/OAI/Analysis/BiholderTransport/Regularity/MovingCrossing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MovingCrossing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma movingFixedJoinMiddle_strict_crossing {a : M} {b p : Model n} {h : ℝ}
--       (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hh : 0 < h) (hh1 : h < 1)
--       (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
--         ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
--         injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
--       (hright : (1-h) • (sprayFlow h
--         (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
--           (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
--             ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
--         injectivityDomain (sprayFlow h
--           (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
--             (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
--               ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (v : Model n) (hv : ‖v‖=1) :
--       0 < -(fderiv ℝ (movingFixedJoinMiddle a h) (1,(b,p)) (1,0) v v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.movingFixedJoinMiddle` (definitions bundle `OAIQ232A012` of this split); `OAI.WeakMTWTransport.sprayFlow` (definitions bundle `OAIQ232A013` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.injectivityDomain` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MovingCrossing.lean (declaration OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing)

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
import Definitions.Def_OAIQ232A013

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingFixedJoinMiddle_strict_crossing {a : M} {b p : Model n} {h : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hh : 0 < h) (hh1 : h < 1)
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (1-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (v : Model n) (hv : ‖v‖=1) :
    0 < -(fderiv ℝ (movingFixedJoinMiddle a h) (1,(b,p)) (1,0) v v) := by
  sorry

end WeakMTWTransport

end

end OAI
end
