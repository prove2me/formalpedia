-- Prove2me | Theorems.Thm_OAI_Problem310Support_positive_scale_normalization
-- name    : OAI.Problem310Support.positive_scale_normalization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:13:00.863982+00:00
-- url     : https://prove2.me/theorems/778ff345-7a18-4bc7-b581-972a151d0126
-- title:
--   Every positive scale can be normalized into $[1,2]$ by powers of two
-- statement:
--   For every real number $s>0$ there exist natural numbers $j,m\ge0$ such that
--
--   $$
--   s\cdot2^{j}\cdot2^{-m}\in[1,2].
--   $$
--
--   This normalization is how a general positive scale is reduced to a scale in the fixed range $[1,2]$. In the dyadic avoidance argument the factor $2^{j}$ corresponds to magnifying by the dilation $x\mapsto2^jx$, while the factor $2^{-m}$ is absorbed by passing to a tail of the dyadic sequence, since $s\,2^{-(m+n)}=(s\,2^{-m})\,2^{-n}$. Two natural-number exponents are used, rather than a single integer exponent, so that both operations are indexed by $\mathbb{N}$.
--
--   **Formalization Note** The factor $2^{-m}$ is written as $(2^{-1})^{m}$ and $[1,2]$ is the closed interval `Icc 1 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean#L36-L51

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

theorem OAI.Problem310Support.positive_scale_normalization {s : ℝ} (hs : 0 < s) :
    ∃ j m : ℕ, (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) ∈ Icc (1 : ℝ) 2 := by sorry
