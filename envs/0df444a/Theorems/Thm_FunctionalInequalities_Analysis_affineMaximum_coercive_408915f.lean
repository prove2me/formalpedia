-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_408915f
-- name    : FunctionalInequalities.Analysis.affineMaximum_coercive_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:44.969535+00:00
-- url     : https://prove2.me/theorems/a0ae5964-84f3-47d1-9ff3-4c49d86532bc
-- title:
--   Coercive Lower Bound for a Finite Affine Maximum
-- statement:
--   This is a geometric coercivity statement for a finite affine maximum.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $s\subseteq E$ be a nonempty finite set, and assume
--
--   $$0\in\operatorname{int}\bigl(\operatorname{conv}(s)\bigr).$$
--
--   Then there exists $c>0$ such that, for every function $a:E\to\mathbb R$, every $M\in\mathbb R$, and every $y\in E$, if $a(x)\le M$ for all $x\in s$, then
--
--   $$c\|y\|-M\le \operatorname{affineMaximum}(s,a,y),$$
--
--   where `affineMaximum` is the maximum of $\langle x,y\rangle-a(x)$ over $x\in s$. The constant $c$ depends on the finite set and its neighborhood condition, but not on $a$, $M$, or $y$. The vertex intercept bound is required only on the elements of $s$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L51-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, declaration `FunctionalInequalities.Analysis.affineMaximum_coercive`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.affineMaximum_coercive_408915f [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (h0 : (0 : E) ∈ interior (convexHull ℝ (↑s : Set E))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : E → ℝ) (M : ℝ), (∀ x ∈ s, a x ≤ M) →
      ∀ y, c * ‖y‖ - M ≤ affineMaximum s hs a y := by sorry
