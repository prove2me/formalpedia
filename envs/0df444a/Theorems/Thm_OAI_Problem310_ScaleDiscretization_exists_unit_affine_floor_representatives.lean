-- Prove2me | Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_unit_affine_floor_representatives
-- name    : OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:35:10.14296+00:00
-- url     : https://prove2.me/theorems/ae011994-aefe-4cc3-84ba-3eb370b35dc2
-- title:
--   Common representatives in $[1,2]$ for floors of affine functions with slopes at most $D$
-- statement:
--   Let $\iota$ be a finite index set with $|\iota|$ elements, let $D\in\mathbb{N}$, and let $u_i,v_i\in\mathbb{R}$ for $i\in\iota$ satisfy $0\le v_i\le D$ for every $i$.
--
--   **Theorem.** There is a finite set $R\subseteq[1,2]$ with $|R|\le 1+|\iota|\,D$ such that
--
--   $$\forall\,t\in[1,2]\ \ \exists\,t'\in R\ \ \forall\,i\in\iota:\qquad \lfloor u_i+v_it'\rfloor=\lfloor u_i+v_it\rfloor .$$
--
--   This is the normalized form of the affine representative bound: on the scale interval $[1,2]$ a uniform slope bound $D$ gives a natural-number cardinality bound that is linear in the number of functions. It is used with $D$ a power of two to discretize the dilation parameter $t$ of points of the form $x+t\,2^{-n}$.
--
--   **Formalization Note** $|\iota|$ is `Fintype.card ι`, the interval is `Set.Icc (1 : ℝ) 2`, and in the hypothesis $v_i\le D$ the natural number $D$ is cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean#L106-L128

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

theorem OAI.Problem310.ScaleDiscretization.exists_unit_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (u v : ι → ℝ) (D : ℕ) (hv : ∀ i, 0 ≤ v i) (hD : ∀ i, v i ≤ (D : ℝ)) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * D ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by sorry
