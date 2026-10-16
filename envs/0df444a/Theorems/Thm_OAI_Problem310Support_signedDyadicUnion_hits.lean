-- Prove2me | Theorems.Thm_OAI_Problem310Support_signedDyadicUnion_hits
-- name    : OAI.Problem310Support.signedDyadicUnion_hits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:13:57.073532+00:00
-- url     : https://prove2.me/theorems/6f74d394-de16-4065-b9e9-9fde7953625b
-- title:
--   Normalized dyadic hitting at every magnification gives hitting at all nonzero scales
-- statement:
--   Let $H=(H_j)_{j\in\mathbb{N}}$ be a sequence of subsets of $\mathbb{R}$. Its **signed dyadic union** is the set
--   $$
--   U(H)=\bigcup_{j=0}^{\infty}\Bigl(\{x\in\mathbb{R} : 2^jx\in H_j\}\cup\{x\in\mathbb{R} : -2^jx\in H_j\}\Bigr),
--   $$
--   that is, the union over $j$ of the pullbacks of $H_j$ under the two dilations $x\mapsto 2^jx$ and $x\mapsto-2^jx$.
--
--   Assume that every $H_j$ meets every normalized dyadic configuration: for every $j\in\mathbb{N}$, every $x\in\mathbb{R}$ and every $t\in[1,2]$ there is an integer $n\ge1$ with $x+t\,2^{-n}\in H_j$. Then $U(H)$ meets every affine copy of the dyadic sequence with nonzero scale:
--
--   $$
--   \forall x\in\mathbb{R}\ \ \forall s\in\mathbb{R}\setminus\{0\}\ \ \exists n\ge1:\qquad x+s\,2^{-n}\in U(H).
--   $$
--
--   The implication is purely algebraic; no openness, periodicity or measure condition is involved. In the dyadic avoidance argument the $H_j$ are open sets of small density, so $U(H)$ is a small open set meeting every set $\{x+s\,2^{-n} : n\ge1\}$ with $s\ne0$, and the complement of $U(H)$ in $[0,1]$ avoids all of them.
--
--   **Formalization Note** The signed dyadic union is `signedDyadicUnion H`, and $2^{-n}$ is written as $(2^{-1})^{n}$; the indices $j$ and $n$ are natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean#L76-L103

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

open OAI OAI.Problem310Support
open Set MeasureTheory

theorem OAI.Problem310Support.signedDyadicUnion_hits {H : ℕ → Set ℝ}
    (hH : ∀ j (x t : ℝ), t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by sorry
