-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_volume_convexHull_closedBall_union_singleton_ge_408915f
-- name    : FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:40.150397+00:00
-- url     : https://prove2.me/theorems/16469f4c-0294-4ae3-baa3-a399a97ecefe
-- title:
--   Volume Lower Bound for a Ball Cone
-- statement:
--   This gives the volume lower bound for the convex hull of a ball and an exterior point.
--
--   Let $E$ be a finite-dimensional real inner-product space with its measurable and Borel structures, and write $n=\dim E$. There exists $c>0$, depending only on $E$, such that for every $r>0$ and every $q\in E$ with $r\le\|q\|$,
--
--   $$
--   \operatorname{ofReal}\!\left(c\,r^{n-1}\|q\|\right)
--   \le
--   \operatorname{vol}\!\left(\operatorname{convHull}\left(\overline B(0,r)\cup\{q\}\right)\right).
--   $$
--
--   The volume values are in $[0,\infty]$ (`ENNReal`), and the real expression is embedded using `ofReal`. The declaration is `exists_pos_volume_convexHull_closedBall_union_singleton_ge`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L746-L1054 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge`; the repository is private at upload time).

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
section LT11C4ConeVolume
open MeasureTheory Set Metric
open scoped ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_408915f {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by sorry
