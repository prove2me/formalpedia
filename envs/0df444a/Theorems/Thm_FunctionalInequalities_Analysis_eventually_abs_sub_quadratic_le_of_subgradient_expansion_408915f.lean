-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eventually_abs_sub_quadratic_le_of_subgradient_expansion_408915f
-- name    : FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:56.975995+00:00
-- url     : https://prove2.me/theorems/b088fef7-294e-4f7d-aef2-193c03f22add
-- title:
--   Subgradient Expansion Implies Quadratic Function Expansion
-- statement:
--   This is an auxiliary second-order expansion lemma for convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be convex on $E$, let $x,p\in E$, and let $B:E\to E$ be continuous linear. Assume that for every $\varepsilon>0$, for all $y$ sufficiently near $x$, every subgradient $q$ of $f$ at $y$ satisfies
--
--   $$\|q-p-B(y-x)\|\le \varepsilon\|y-x\|.$$
--
--   Then, for every $\varepsilon>0$, for all $y$ sufficiently near $x$,
--
--   $$\left|f(y)-f(x)-\langle p,y-x\rangle-\frac12\langle B(y-x),y-x\rangle\right|\le \varepsilon\|y-x\|^2.$$
--
--   The declaration `eventually_abs_sub_quadratic_le_of_subgradient_expansion` converts a first-order local estimate on all subgradients into a second-order local estimate for the function. The same symbol $\varepsilon$ is used in both quantified conclusions, exactly as in the Lean statement.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1434-L1543 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion`; the repository is private at upload time).

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
section LT12D5SubgradientExpansionTaylor
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

theorem FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_408915f [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) {x p : E} {B : E →L[ℝ] E}
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by sorry
