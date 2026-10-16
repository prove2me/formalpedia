-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_largeIntersectionTail_le
-- name    : OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:13.694306+00:00
-- url     : https://prove2.me/theorems/a41360e1-5a3b-4be0-b599-392af43be0d9
-- title:
--   Exponential bound on the binomial upper tail $\sum_{2r>m}\binom{m}{r}q^r$ for $0\le q\le e^{-50}$
-- statement:
--   For $m\in\mathbb{N}$ and $q\in\mathbb{R}$ define the *large-intersection tail*
--   $$
--   T(m,q)=\sum_{\substack{0\le r\le m\\ 2r>m}}\binom{m}{r}q^{r}.
--   $$
--
--   **Theorem.** If $0\le q\le e^{-50}$, then for every $m\in\mathbb{N}$
--   $$
--   T(m,q)\le 2^{m}e^{-25m}.
--   $$
--
--   The sum $T(m,q)$ is the natural union bound for the event that more than half of a fixed $m$-element set is hit, when every fixed $r$-element subset is hit with probability at most $q^{r}$. The lemma turns the smallness of $q$ into exponential decay in $m$. In the local-failure estimate of the threshold argument it is applied with $q=a/\rho$, the ratio of a spread parameter $a$ to a sampling density $\rho$, and then multiplied by a factor $e^{10m}$.
--
--   **Formalization Note** The sum is over $r$ in `Finset.range (m + 1)` with the condition `m < 2 * r` as an `if`; $m=0$ is allowed (then $T(0,q)=0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean#L63-L77

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

theorem OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le {m : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-50)) :
    largeIntersectionTail m q ≤ (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by sorry
