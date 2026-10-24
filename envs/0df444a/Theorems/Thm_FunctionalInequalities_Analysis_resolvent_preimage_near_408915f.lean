-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_resolvent_preimage_near_408915f
-- name    : FunctionalInequalities.Analysis.resolvent_preimage_near_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:10.645038+00:00
-- url     : https://prove2.me/theorems/761ce735-6ae8-46ff-83ab-313651f493f5
-- title:
--   Local Preimage Control for a Firmly Monotone Resolvent
-- statement:
--   This private lemma is a technical local inverse estimate.
--
--   Let $E$ be a real inner-product space, let $P:E\to E$, and assume the firm monotonicity inequality
--
--   $$\|P(a)-P(b)\|^2\le\langle P(a)-P(b),a-b\rangle.$$
--
--   Let $z\in E$ and let $c,\delta>0$. Suppose that every $w$ with $\|w-z\|<\delta$ satisfies
--
--   $$c\|w-z\|\le\|P(w)-P(z)\|.$$
--
--   Then any $a\in E$ satisfying
--
--   $$\|P(a)-P(z)\|<\frac{c^2\delta}{2}$$
--
--   must also satisfy
--
--   $$\|a-z\|<\delta.$$
--
--   The private declaration `resolvent_preimage_near` is used to transfer a sufficiently small image neighborhood into the corresponding domain neighborhood.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L73-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `_private.FunctionalInequalities.Analysis.Convex.SecondOrder.0.FunctionalInequalities.Analysis.resolvent_preimage_near`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.resolvent_preimage_near_408915f {P : E → E} {z : E}
    (hm : ∀ a b, ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hl : ∀ w, ‖w - z‖ < δ → c * ‖w - z‖ ≤ ‖P w - P z‖)
    (a : E) (ha : ‖P a - P z‖ < c ^ 2 * δ / 2) :
    ‖a - z‖ < δ := by sorry
