-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_zero_prefix_positive_suffix
-- name    : OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:13:36.120803+00:00
-- url     : https://prove2.me/theorems/3dbb6408-99d3-4b78-9c66-ddbc517299ee
-- title:
--   A monotone capacity sequence splits into a zero prefix and a positive suffix
-- statement:
--   Let $m:\mathbb{N}\to\mathbb{N}$ and $d\in\mathbb{N}$, and suppose that $m$ is nondecreasing on the initial segment $\{0,1,\dots,d-1\}$, that is, $m(i)\le m(j)$ whenever $i\le j<d$. Then there is an index $k$ with $0\le k\le d$ such that
--
--   $$
--   m(i)=0\quad\text{for all } i<k \qquad\text{and}\qquad m(j)>0\quad\text{for all } j \text{ with } k\le j<d.
--   $$
--
--   Either part may be empty: $k=0$ when $m(0)>0$, and $k=d$ (so that there is no positive part) when $m$ vanishes on the whole segment.
--
--   In the covering argument for probability trees, $m(i)$ is the halved label capacity of level $i$ of a tree of depth $d$. Since the halved capacities are nondecreasing in the level, the levels whose capacity has dropped to $0$ form an initial block; the lemma locates this block, which can then be deleted, leaving a tree all of whose remaining levels have positive capacity.
--
--   **Formalization Note** Monotonicity is Mathlib's `MonotoneOn m (Set.Iio d)`. The positive part is stated with an index shift, as $0<m(i+k)$ for all $i<d-k$ with natural-number subtraction $d-k$; since $k\le d$ this subtraction is exact and the condition says precisely that $m(j)>0$ for $k\le j<d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean#L23-L47

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Classical

theorem OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix (m : ℕ → ℕ) (d : ℕ)
    (hmono : MonotoneOn m (Set.Iio d)) :
    ∃ k, k ≤ d ∧ (∀ i, i < k → m i = 0) ∧
      (∀ i, i < d - k → 0 < m (i + k)) := by sorry
