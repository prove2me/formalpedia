-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_local_failure_exponential_combine
-- name    : OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:42:01.100172+00:00
-- url     : https://prove2.me/theorems/acd37594-86a7-4aec-a66d-efd1afa23773
-- title:
--   Combining two exponential bounds: $e^{-10m}+e^{10m}2^{m}e^{-25m}\le e^{-9m}$ for $m\ge 1$
-- statement:
--   **Theorem.** For every natural number $m\ge 1$,
--   $$
--   e^{-10m}+e^{10m}\cdot 2^{m}\cdot e^{-25m}\le e^{-9m}.
--   $$
--
--   In the local-failure estimate of the threshold argument, a failure at a node whose arc labels have at most $m$ elements is split into two cases: a small-density case, of probability at most $e^{-10m}$, and a large-fragment case, bounded by $e^{10m}$ times the binomial tail bound $2^{m}e^{-25m}$. This numerical lemma adds the two contributions and yields the single bound $e^{-9m}$.
--
--   **Formalization Note** $m$ is a natural number cast to $\mathbb{R}$, and the hypothesis is `1 ≤ m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean#L79-L101

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset

theorem OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
      Real.exp (-9 * (m : ℝ)) := by sorry
