-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_unit_inner_le_infDist_frontier_408915f
-- name    : FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:39.471284+00:00
-- url     : https://prove2.me/theorems/adce9c57-3e27-46d1-8119-c738a831ea94
-- title:
--   Supporting Direction at the Nearest Frontier
-- statement:
--   This formalizes the supporting half-space estimate for a bounded open convex set.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space, let $\Omega\subseteq E$ be open, convex, and bounded, and let $x_0\in\Omega$. Then there exists a unit vector $e\in E$ such that every $x\in\Omega$ satisfies
--
--   $$
--   \langle x-x_0,e\rangle\le\operatorname{infDist}(x_0,\partial\Omega).
--   $$
--
--   The declaration is `exists_unit_inner_le_infDist_frontier`. Here `infDist` is the distance from $x_0$ to the frontier, and the conclusion is existential rather than a uniqueness statement about the supporting direction.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L620-L731 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier`; the repository is private at upload time).

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
section LT11C3NearestBoundaryHalfspace
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

theorem FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω) := by sorry
