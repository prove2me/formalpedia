-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_exists_reverse_exp_divided_isotropic_gain
-- name    : OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:44:05.711194+00:00
-- url     : https://prove2.me/theorems/89760afb-2c3f-49ca-8a92-2e98f274546f
-- title:
--   OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain` of [lean/OAI/Analysis/BiholderTransport/Coordinates/ReverseIsotropicGain.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/ReverseIsotropicGain.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle Module`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma exists_reverse_exp_divided_isotropic_gain {x y : M} {h s t a c : ℝ}
--       {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
--       (hh : 0<h) (hhs : h < s) (hht : h<t)
--       (hps : s • p∈injectivityDomain x) (hpt : t • p∈injectivityDomain x)
--       (hq : q∈injectivityDomain y) (hpx : riemannianExp x (s • p)=y)
--       (hqy : riemannianExp y q=x) (ha : 0<a) (hc : 0 ≤ c)
--       (hcross : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
--         c*‖v‖^2≤fixedJoinMiddle x h s p v v-fixedJoinMiddle x h t p v v)
--       (hbound : s*‖normalEndpointMixedOperator x y (h/s) (s • p)‖≤a) :
--       ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
--         ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
--         (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
--         ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
--           (c/a^2)*‖w‖^2 ≤ hessianValue x (s • p) (fderiv ℝ R q w)/s-
--             hessianValue x (t • p) (fderiv ℝ R q w)/t
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.fixedJoinMiddle` and `OAI.WeakMTWTransport.normalEndpointMixedOperator` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.hessianValue` (definitions bundle `OAIQ232A001` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.exists_uniform_center_support_pullback` and `OAI.WeakMTWTransport.exists_uniform_true_center_gain` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/ReverseIsotropicGain.lean (declaration OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain)

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
import Definitions.Def_OAIQ232A001

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteReverseGain_r7edca7_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma exists_reverse_exp_divided_isotropic_gain {x y : M} {h s t a c : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hhs : h < s) (hht : h<t)
    (hps : s • p∈injectivityDomain x) (hpt : t • p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x (s • p)=y)
    (hqy : riemannianExp y q=x) (ha : 0<a) (hc : 0 ≤ c)
    (hcross : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
      c*‖v‖^2≤fixedJoinMiddle x h s p v v-fixedJoinMiddle x h t p v v)
    (hbound : s*‖normalEndpointMixedOperator x y (h/s) (s • p)‖≤a) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
        (c/a^2)*‖w‖^2 ≤ hessianValue x (s • p) (fderiv ℝ R q w)/s-
          hessianValue x (t • p) (fderiv ℝ R q w)/t := by
  sorry

end WeakMTWTransport

end

end OAI
end
