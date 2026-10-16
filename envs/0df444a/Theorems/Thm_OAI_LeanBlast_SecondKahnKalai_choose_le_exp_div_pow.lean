-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_choose_le_exp_div_pow
-- name    : OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:15.299755+00:00
-- url     : https://prove2.me/theorems/c446051d-d0a5-4aab-8696-0f04e475f860
-- title:
--   Binomial coefficient bound $\binom{h}{r}\le(eh/r)^{r}$
-- statement:
--   **Theorem.** For natural numbers $h$ and $r$ with $r\ge 1$,
--   $$
--   \binom{h}{r}\le\Bigl(\frac{e\,h}{r}\Bigr)^{r},
--   $$
--   where $e=\exp(1)$ and $\binom{h}{r}=0$ when $r>h$.
--
--   This is the standard upper estimate for binomial coefficients. In the threshold argument it bounds the number of $r$-element subsets of an $h$-element set, and hence the number of copies of an $r$-element set lying inside an $h$-element set. With $h\le 17r$ it gives $\binom{h}{r}\le(17e)^{r}$, which is small compared with $128^{r}$; this comparison is how the predecessor construction shows that a maximizing predecessor has fewer than one seventeenth of the elements of the current set.
--
--   **Formalization Note** The inequality is stated in $\mathbb{R}$ for the natural-number binomial coefficient `h.choose r` cast to a real number; $h=0$ is allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean#L25-L45

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

theorem OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow (h r : ℕ) (hr : 0 < r) :
    (h.choose r : ℝ) ≤ (Real.exp 1 * (h : ℝ) / (r : ℝ)) ^ r := by sorry
