-- Prove2me | Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_monotone_representatives
-- name    : OAI.Problem310.ScaleDiscretization.exists_monotone_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:33:53.128103+00:00
-- url     : https://prove2.me/theorems/cc67d00a-54f6-437e-865f-884c480876ad
-- title:
--   A monotone family of integer vectors on an interval has few common representatives
-- statement:
--   Let $\alpha$ be a linearly ordered set, let $\iota$ be a finite index set, let $a\le b$ in $\alpha$, and write $[a,b]=\{t\in\alpha:a\le t\le b\}$. Let $f:\alpha\to\mathbb{Z}^\iota$, $t\mapsto(f(t)_i)_{i\in\iota}$, be monotone on $[a,b]$ for the coordinatewise order: $s\le t$ with $s,t\in[a,b]$ implies $f(s)_i\le f(t)_i$ for every $i\in\iota$.
--
--   **Theorem.** There is a finite set $R\subseteq[a,b]$ such that
--
--   $$|R|\le 1+\sum_{i\in\iota}f(b)_i-\sum_{i\in\iota}f(a)_i\qquad\text{and}\qquad \forall\,t\in[a,b]\ \ \exists\,t'\in R:\ f(t')=f(t).$$
--
--   So a monotone integer-vector-valued function on an interval takes at most $1+\sum_i\bigl(f(b)_i-f(a)_i\bigr)$ distinct values, and one can choose a representative parameter for each of them inside the interval, endpoints included. This is the combinatorial core of the scale discretization: applied to simultaneous floor functions it shows that a continuous parameter can be replaced by a small finite set without changing any of the floors.
--
--   **Formalization Note** The cardinality bound is stated as `((∑ i, f b i) + 1 - ∑ i, f a i).toNat`; by monotonicity this integer is at least $1$, so the truncation of `Int.toNat` at $0$ plays no role. Monotonicity is `MonotoneOn f (Set.Icc a b)` for the pointwise order on `ι → ℤ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean#L27-L63

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

theorem OAI.Problem310.ScaleDiscretization.exists_monotone_representatives {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    (a b : α) (hab : a ≤ b) (f : α → ι → ℤ)
    (hf : MonotoneOn f (Set.Icc a b)) :
    ∃ R : Finset α,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ ((∑ i, f b i) + 1 - ∑ i, f a i).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R, f t' = f t := by sorry
