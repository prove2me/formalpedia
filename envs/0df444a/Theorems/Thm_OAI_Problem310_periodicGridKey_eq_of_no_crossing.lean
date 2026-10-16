-- Prove2me | Theorems.Thm_OAI_Problem310_periodicGridKey_eq_of_no_crossing
-- name    : OAI.Problem310.periodicGridKey_eq_of_no_crossing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:17:35.576045+00:00
-- url     : https://prove2.me/theorems/618ae2a1-c895-48a3-86f7-b4c6530a79d8
-- title:
--   Periodic grid labels do not change between consecutive grid points
-- statement:
--   For a real number $x$ let $\{x\}=x-\lfloor x\rfloor\in[0,1)$ denote its fractional part. For a positive integer $q$ the **periodic grid key** of $x$ is
--   $$
--   \kappa_q(x)=\bigl\lfloor q\,\{x\}\bigr\rfloor\in\{0,1,\dots,q-1\},
--   $$
--   the index $i$ of the cell $[i/q,(i+1)/q)$ of the $q$-cell grid on $[0,1)$ that contains $\{x\}$; it is a 1-periodic function of $x$.
--
--   Let $q\ge1$ be an integer and let $x\le y$ be real numbers such that no grid point $k/q$ with $k\in\mathbb{Z}$ lies in the half-open interval $(x,y]$. Then
--
--   $$
--   \kappa_q(x)=\kappa_q(y).
--   $$
--
--   Because the interval is open at its left end, $x$ itself may be a grid point. The lemma is the basic stability principle for grid labels: moving a point to the right without crossing a grid boundary $k/q$ leaves its cell label unchanged. It is used to show that dyadic trial points to the right of a center read the same grid label as the center.
--
--   **Formalization Note** The key is `periodicGridKey q x`, defined as $\lfloor q\,\mathrm{fract}(x)\rfloor$ for a real parameter $q$; here $q$ is a natural number cast to $\mathbb{R}$, with the explicit hypothesis $0<q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean#L59-L81

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry

open OAI OAI.Problem310

theorem OAI.Problem310.periodicGridKey_eq_of_no_crossing (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hxy : x ≤ y) (hcross : ∀ k : ℤ, (k : ℝ) / q ∉ Set.Ioc x y) :
    periodicGridKey q x = periodicGridKey q y := by sorry
