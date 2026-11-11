-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_eventual_lower_bound_of_center_gain
-- name    : OAI.WeakMTWTransport.eventual_lower_bound_of_center_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:40:45.706195+00:00
-- url     : https://prove2.me/theorems/bce36ef1-afcf-4371-9635-933cd3efd116
-- title:
--   OAI.WeakMTWTransport.eventual_lower_bound_of_center_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.eventual_lower_bound_of_center_gain` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumLowerBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumLowerBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma eventual_lower_bound_of_center_gain {a:M} {q:TangentSpace 𝓘(ℝ,Model n) a}
--       {A C:ℝ} (hA:0 ≤ A) (hC:C ≤ 0) {H:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ}
--       (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
--         A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
--         C*(inner ℝ q (show TangentSpace 𝓘(ℝ,Model n) a from d))^2-ε*‖d‖^2 ≤ H k d d) :
--       ∃CH:ℝ,0 ≤ CH ∧ ∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ H k d d
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.Model` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumLowerBound.lean (declaration OAI.WeakMTWTransport.eventual_lower_bound_of_center_gain)

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
section MaximumLowerBound
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance lowerDualGroup_r70c1d6_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance lowerDualSpace_r70c1d6_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance lowerBilinearGroup_r70c1d6_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance lowerBilinearSpace_r70c1d6_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
omit [Nonempty M] in
lemma eventual_lower_bound_of_center_gain {a:M} {q:TangentSpace 𝓘(ℝ,Model n) a}
    {A C:ℝ} (hA:0 ≤ A) (hC:C ≤ 0) {H:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
      C*(inner ℝ q (show TangentSpace 𝓘(ℝ,Model n) a from d))^2-ε*‖d‖^2 ≤ H k d d) :
    ∃CH:ℝ,0 ≤ CH ∧ ∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ H k d d := by
  sorry

end MaximumLowerBound
end WeakMTWTransport

end
end

end OAI
end
