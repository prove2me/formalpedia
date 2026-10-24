-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_of_ae_gradient_mem_408915f
-- name    : FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:49.635248+00:00
-- url     : https://prove2.me/theorems/1c3cdb22-0362-4df1-aaf3-09e09612a471
-- title:
--   Subgradients Lie In Closed Convex Gradient Range
-- statement:
--   This proves containment of every subgradient in a closed convex range of the almost-everywhere gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Let $K\subseteq E$ be closed and convex, and assume
--   $$\nabla u(x)\in K\quad\text{for almost every }x\text{ with respect to volume}.$$
--   If $x,p\in E$ satisfy
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y\in E,$$
--   then
--   $$p\in K.$$
--
--   This is a support-and-closure principle used to control subgradient images.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L145-L186 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section SubgradientRange
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K := by sorry
