-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_normalized_count_score_bound
-- name    : OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:45.47327+00:00
-- url     : https://prove2.me/theorems/01080509-8edf-4bc4-a67c-281e5a2b5f52
-- title:
--   Arithmetic bound on the normalized copy-count score: $\frac{a/m}{(128q)^{r}}\le\frac{2\binom{h}{r}}{128^{r}}$
-- statement:
--   Let $a,m,h,r$ be natural numbers and $q$ a real number with $q>0$ and $m>0$.
--
--   **Theorem.** If
--   $$
--   a\le\binom{h}{r}\qquad\text{and}\qquad\tfrac12\le m\,q^{r},
--   $$
--   then
--   $$
--   \frac{a/m}{(128\,q)^{r}}\le\frac{2\binom{h}{r}}{128^{r}}.
--   $$
--
--   This is the arithmetic core of the predecessor estimate. There, a candidate set $S$ with $r$ elements inside a current set $I$ with $h$ elements receives the score $\pi_I(S)/(128q)^{r}$, where $\pi_I(S)$ is the probability that a uniformly random copy of $I$ (under a finite group action) contains $S$. By the copy-incidence identity, $\pi_I(S)=a/m$ with $a$ the number of copies of $S$ inside $I$, which is at most $\binom{h}{r}$, and $m$ the total number of copies of $S$; the hypothesis $\tfrac12\le m q^{r}$ is the expectation constraint at density $q$. The lemma turns these two facts into the score bound $2\binom{h}{r}/128^{r}$.
--
--   **Formalization Note** All of $a,m,h,r$ are natural numbers cast to $\mathbb{R}$, and the binomial coefficient is `h.choose r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean#L72-L88

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators

theorem OAI.LeanBlast.SecondKahnKalai.normalized_count_score_bound {a m h r : ℕ} {q : ℝ}
    (hq : 0 < q) (hm : 0 < m) (ha : a ≤ h.choose r)
    (he : (1 / 2 : ℝ) ≤ (m : ℝ) * q ^ r) :
    ((a : ℝ) / (m : ℝ)) / (128 * q) ^ r ≤
      2 * (h.choose r : ℝ) / (128 : ℝ) ^ r := by sorry
