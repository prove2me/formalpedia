-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_compact_sections_subset_and_shrink_408915f
-- name    : FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:00.264091+00:00
-- url     : https://prove2.me/theorems/f782c949-32ee-4c92-a666-47d8f1fc5b8c
-- title:
--   Compactness and Shrinking of Exposed Sections
-- statement:
--   This formalizes the exposed-point section estimate used in the Caffarelli argument.
--
--   Let $E$ be finite-dimensional, let $u:E\to\mathbb R$ be convex, and let $x_0,p\in E$ satisfy
--
--   $$
--   u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y.
--   $$
--
--   Assume the contact set $C=\{x:u(x)=u(x_0)+\langle p,x-x_0\rangle\}$ is compact. Let $x_e\in C$, let $\|\theta\|=1$, assume $x_e$ is exposed in direction $\theta$, and let $h>0$. For
--
--   $$
--   S_\varepsilon=\{x:u(x)-u(x_0)-\langle p,x-x_0\rangle<\varepsilon(\langle x-x_e,\theta\rangle+h)\},
--   $$
--
--   there is a compact set $Q$ containing $S_\varepsilon$ for all sufficiently small positive $\varepsilon$. Moreover, for every $\delta>0$, sufficiently small positive $\varepsilon$ give
--
--   $$
--   S_\varepsilon\subseteq\operatorname{cthickening}_\delta\big(C\cap\{x:-h\le\langle x-x_e,\theta\rangle\}\big).
--   $$
--
--   The declaration is `exists_compact_sections_subset_and_shrink`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L175-L344 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11E3SectionsShrink
open Set Metric Filter
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

theorem FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink_408915f [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {x₀ p : E} (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y)
    (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫}) {xe θ : E}
    (hxe : u xe = u x₀ + ⟪p, xe - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ xe → ⟪x - xe, θ⟫ < 0) {h : ℝ} (hh : 0 < h) :
    (∃ Q : Set E, IsCompact Q ∧ ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆ Q) ∧
    ∀ δ > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆
        cthickening δ ({x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - xe, θ⟫}) := by sorry
