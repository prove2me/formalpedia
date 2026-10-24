-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_mem_subgradientImage_of_affine_le_of_nonneg_frontier_408915f
-- name    : FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:39.865141+00:00
-- url     : https://prove2.me/theorems/8b6b7dee-2360-440e-a707-d071bbfe7db3
-- title:
--   Sliding Lemma for the Subgradient Image
-- statement:
--   This formalizes the sliding lemma for the Alexandrov maximum principle.
--
--   Let $E$ be finite-dimensional, let $u:E\to\mathbb R$ be convex, and let $\Omega\subseteq E$ be open and bounded. Assume:
--
--   1. $u\ge0$ on $\partial\Omega$.
--   2. $x_0\in\Omega$ and $u(x_0)<0$.
--   3. For some $p\in E$, the affine function satisfies
--      $$u(x_0)+\langle p,x-x_0\rangle\le0$$
--      for every $x\in\overline\Omega$.
--
--   Then $p$ belongs to the subgradient image of $u$ over $\Omega$:
--
--   $$
--   p\in\operatorname{subgradientImage}(u,\Omega).
--   $$
--
--   The declaration is `mem_subgradientImage_of_affine_le_of_nonneg_frontier`. It asserts membership in the image, not a specified point realizing the subgradient.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L450-L605 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier`; the repository is private at upload time).

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
section LT11C2AlexandrovSliding
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

theorem FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
    {p : E} (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ subgradientImage u Ω := by sorry
