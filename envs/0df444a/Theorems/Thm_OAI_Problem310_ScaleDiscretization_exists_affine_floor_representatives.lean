-- Prove2me | Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_affine_floor_representatives
-- name    : OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:34:38.000553+00:00
-- url     : https://prove2.me/theorems/b83fbd03-aaff-4290-b906-b5dee9fed0d0
-- title:
--   Few common representatives for the floors of finitely many nondecreasing affine functions
-- statement:
--   Let $\iota$ be a finite index set, let $a\le b$ be real numbers, and let $u_i,v_i\in\mathbb{R}$ for $i\in\iota$, with $v_i\ge0$ for every $i$. Consider the nondecreasing affine functions $t\mapsto u_i+v_it$ on $[a,b]$.
--
--   **Theorem.** There is a finite set $R\subseteq[a,b]$ with
--
--   $$|R|\le 1+\sum_{i\in\iota}\bigl\lceil v_i(b-a)\bigr\rceil$$
--
--   such that for every $t\in[a,b]$ there is $t'\in R$ with $\lfloor u_i+v_it'\rfloor=\lfloor u_i+v_it\rfloor$ simultaneously for all $i\in\iota$.
--
--   Thus the vector of integer parts $\bigl(\lfloor u_i+v_it\rfloor\bigr)_{i\in\iota}$ takes at most $1+\sum_i\lceil v_i(b-a)\rceil$ values on $[a,b]$, and each value is attained on a fixed finite subset of the interval. The bound depends only on the total displacements $v_i(b-a)$, not on the offsets $u_i$.
--
--   **Formalization Note** The bound is stated as `(1 + ∑ i, ⌈v i * (b - a)⌉).toNat`; since $v_i\ge0$ and $b\ge a$, every ceiling is nonnegative, so the truncation at $0$ is immaterial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean#L76-L104

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel

open OAI OAI.Problem310
universe u_α u_ι
open scoped BigOperators

theorem OAI.Problem310.ScaleDiscretization.exists_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (u v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ (1 + ∑ i, ⌈v i * (b - a)⌉).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by sorry
