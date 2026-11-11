-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_density_original_center_good
-- name    : OAI.WeakMTWTransport.exists_density_original_center_good
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:00:32.477223+00:00
-- url     : https://prove2.me/theorems/60c932c7-e78d-4ba4-bfbe-0ae82decdc94
-- title:
--   OAI.WeakMTWTransport.exists_density_original_center_good: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_density_original_center_good` of [lean/OAI/Analysis/BiholderTransport/Volume/DensityOriginalJets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/DensityOriginalJets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma exists_density_original_center_good {lam cap:ℝ} (hlam:0<lam) (hcap:lam ≤ cap) :
--       ∃χ>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
--         uv∈densityDualClass (metricVolume n) lam cap x0 →
--         ∀ᵐ y ∂metricVolume n,OriginalCenterGood (n:=n) uv.1 χ y
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.OriginalCenterGood` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/DensityOriginalJets.lean (declaration OAI.WeakMTWTransport.exists_density_original_center_good)

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
import Definitions.Def_OAIQ232A017

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section DensityOriginalJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance densityOriginalFinite_rbdaead_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance densityOriginalComplete_rbdaead_1 (x:M) : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) :=
  FiniteDimensional.complete ℝ _
lemma exists_density_original_center_good {lam cap:ℝ} (hlam:0<lam) (hcap:lam ≤ cap) :
    ∃χ>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ᵐ y ∂metricVolume n,OriginalCenterGood (n:=n) uv.1 χ y := by
  sorry
end DensityOriginalJets
end WeakMTWTransport

end
end

end OAI
end
