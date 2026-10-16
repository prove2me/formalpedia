-- Prove2me | Theorems.Thm_OAI_Problem310_dyadicGridKey_eq_of_stable
-- name    : OAI.Problem310.dyadicGridKey_eq_of_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:18:45.953143+00:00
-- url     : https://prove2.me/theorems/501d22c6-a222-481c-9198-995a9635489f
-- title:
--   A grid-stable center keeps its dyadic grid label at all later trial points
-- statement:
--   For a real number $x$ let $\{x\}=x-\lfloor x\rfloor$ be its fractional part. For $b\in\mathbb{N}$ the **dyadic grid key** of $x$ is
--   $$
--   D_b(x)=\bigl\lfloor 2^{b+2}\{x\}\bigr\rfloor\in\{0,1,\dots,2^{b+2}-1\},
--   $$
--   the label of the cell of the grid with $2^{b+2}$ cells per unit period that contains $x$ modulo $1$.
--
--   Let $a,b,n\in\mathbb{N}$ with $a\le n$, let $t\in[1,2]$ and $x\in\mathbb{R}$. Suppose no grid point $k/2^{b+2}$ with $k\in\mathbb{Z}$ lies in the interval $\bigl(x,\,x+2\cdot2^{-a}\bigr]$. Then
--
--   $$
--   D_b\bigl(x+t\,2^{-n}\bigr)=D_b(x).
--   $$
--
--   In the dyadic construction, the grid with $2^{b+2}$ cells serves a window of scales ending at index $b$, and the hypothesis is the no-crossing stability condition of the center $x$ for a later window starting at index $a$. The lemma says that such a stable center has the same label as all trial points $x+t\,2^{-n}$ with $n\ge a$ and $t\in[1,2]$, so later windows do not disturb the labels read by earlier ones.
--
--   **Formalization Note** The key is `dyadicGridKey b x`, defined as the periodic grid key with $2^{b+2}$ cells; the factor $2^{-n}$ is written as $(2^{-1})^{n}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean#L176-L195

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

theorem OAI.Problem310.dyadicGridKey_eq_of_stable {a b n : ℕ} {x t : ℝ}
    (han : a ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hstable : ∀ k : ℤ, (k : ℝ) / (2 : ℝ) ^ (b + 2) ∉
      Set.Ioc x (x + 2 * ((2 : ℝ)⁻¹) ^ a)) :
    dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey b x := by sorry
