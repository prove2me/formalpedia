-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_le_of_forall_inner_le_408915f
-- name    : FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:39.729585+00:00
-- url     : https://prove2.me/theorems/e6b1631b-05e9-4471-95b4-b220ae5c38ef
-- title:
--   Frontier Distance Bounded by Directional Width
-- statement:
--   This proves that the distance to the frontier is bounded by a one-sided width.
--
--   Let $E$ be a normed real inner-product space, let $S\subseteq E$ be open and bounded, let $x\in S$, and let $\theta$ be a unit vector. If for some $t\in\mathbb R$,
--
--   $$
--   \langle y-x,\theta\rangle\le t\qquad\text{for every }y\in S,
--   $$
--
--   then
--
--   $$
--   \operatorname{infDist}(x,\partial S)\le t.
--   $$
--
--   The declaration is `infDist_frontier_le_of_forall_inner_le`. No finite-dimensionality or convexity assumption appears in the statement.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1685-L1740 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
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
open scoped RealInnerProductSpace ENNReal
section LT11E2InfdistLeWidth
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
    infDist x (frontier S) ≤ t := by sorry
