-- Prove2me | Theorems.Thm_OAI_Problem310_ScaleDiscretization_periodic_floor_eq_of_floor_eq
-- name    : OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:37:44.884955+00:00
-- url     : https://prove2.me/theorems/e8c37476-eb25-4f3e-b78f-9f69bac4065a
-- title:
--   Equal dyadic cells on the line give equal cells of the periodic dyadic grid
-- statement:
--   Let $q\in\mathbb{N}$ and $y,z\in\mathbb{R}$, and write $\{w\}=w-\lfloor w\rfloor\in[0,1)$ for the fractional part of a real number $w$.
--
--   **Theorem.** If $\lfloor 2^qy\rfloor=\lfloor 2^qz\rfloor$, then
--
--   $$\bigl\lfloor 2^q\{y\}\bigr\rfloor=\bigl\lfloor 2^q\{z\}\bigr\rfloor .$$
--
--   The integer $\lfloor 2^qy\rfloor=k$ indexes the cell $[k2^{-q},(k+1)2^{-q})$ of the dyadic grid on $\mathbb{R}$ that contains $y$, while $\lfloor 2^q\{y\}\rfloor\in\{0,\dots,2^q-1\}$ indexes the corresponding cell of the grid on the circle $\mathbb{R}/\mathbb{Z}$. The theorem says that the periodic key is a function of the key on the line, so any statement that two points share a dyadic cell of $\mathbb{R}$ transfers to the periodic keys used to address one-periodic tables.
--
--   **Formalization Note** The fractional part is `Int.fract`, and $2^q$ is the real power `(2 : ℝ) ^ q`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean#L162-L179

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

theorem OAI.Problem310.ScaleDiscretization.periodic_floor_eq_of_floor_eq (q : ℕ) {y z : ℝ}
    (h : ⌊(2 : ℝ) ^ q * y⌋ = ⌊(2 : ℝ) ^ q * z⌋) :
    ⌊(2 : ℝ) ^ q * Int.fract y⌋ = ⌊(2 : ℝ) ^ q * Int.fract z⌋ := by sorry
