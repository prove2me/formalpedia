-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_capacity_failure_sum_lt_one_quarter
-- name    : OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:58:21.963038+00:00
-- url     : https://prove2.me/theorems/fac69b8e-131f-49a4-9b4c-0349cef53e7f
-- title:
--   For capacities with $m_j\ge 1$ and $m_{j+1}\ge 16m_j$, the level failure sum $\sum_j e^{12(m_0+\dots+m_{j-1})-8m_j}$ is below $1/4$
-- statement:
--   Let $m_0,m_1,m_2,\dots$ be natural numbers and let $k\in\mathbb{N}$. Assume that the first $k$ terms are positive and grow at least by a factor $16$:
--   $$
--   m_j\ge 1\quad(0\le j<k),\qquad 16\,m_j\le m_{j+1}\quad(0\le j,\ j+1<k).
--   $$
--
--   **Theorem.** Under these assumptions
--   $$
--   \sum_{j=0}^{k-1}\exp\Bigl(12\sum_{h=0}^{j-1}m_h\;-\;8\,m_j\Bigr)\ <\ \frac14 .
--   $$
--   For $k=0$ the sum is empty, and only $m_0,\dots,m_{k-1}$ enter the statement.
--
--   In the analysis of tree reduction, $m_j$ is the capacity at level $j$ of a depth-$k$ probability tree, and the sum is the closed form of the recursive envelope $E(m_0,m_1,\dots)=e^{-8m_0}+e^{12m_0}E(m_1,m_2,\dots)$ that bounds the probability that one simultaneous reduction step fails: level $j$ contributes a local failure factor $e^{-8m_j}$, multiplied by a factor $e^{12m_h}$ for every earlier level $h<j$. The theorem shows that such a failure has probability less than $1/4$, uniformly in the depth.
--
--   **Formalization Note** The sequence is a function `m : ℕ → ℕ`, the sums are over `Finset.range`, and $\exp$ is `Real.exp`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/CapacityIteration.lean#L320-L346

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset Set

theorem OAI.LeanBlast.SecondKahnKalai.capacity_failure_sum_lt_one_quarter (m : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j, j < k → 1 ≤ m j)
    (hgrowth : ∀ j, j + 1 < k → 16 * m j ≤ m (j + 1)) :
    (∑ j ∈ range k,
      Real.exp (12 * (∑ h ∈ range j, (m h : ℝ)) - 8 * (m j : ℝ))) < (1 / 4 : ℝ) := by sorry
