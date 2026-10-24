-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradient_two_points_eq_zero_408915f
-- name    : FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:49.750121+00:00
-- url     : https://prove2.me/theorems/96d58815-66f5-4d2d-87c1-d41e9c99e61d
-- title:
--   Nullity of Two-Point Subgradient Slopes
-- statement:
--   This gives the Alexandrov null-set statement for repeated subgradients.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Consider the set of slopes that are subgradients at two distinct points:
--   $$S=\left\{p:\exists x\ne y,\ \forall z,\ u(x)+\langle p,z-x\rangle\le u(z),\ \ u(y)+\langle p,z-y\rangle\le u(z)\right\}.$$
--   Then its volume is zero:
--   $$\operatorname{vol}(S)=0.$$
--
--   This is a measure-theoretic uniqueness statement for subgradients and is used in the push-forward Alexandrov identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1109-L1217 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT14ASubgradientAeInjective
open MeasureTheory Set
open scoped RealInnerProductSpace
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

theorem FunctionalInequalities.Analysis.volume_subgradient_two_points_eq_zero_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u) :
    (volume : Measure E) {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
      (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} = 0 := by sorry
