-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectation_intersection_eq_sum
-- name    : OAI.LeanBlast.SecondKahnKalai.expectation_intersection_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:03:28.204981+00:00
-- url     : https://prove2.me/theorems/b8ea400d-7ec1-439a-95c0-7617897a8dd7
-- title:
--   Expectation of a function of $|A_c\cap T|$ through the distribution of the intersection size
-- statement:
--   Let $X$ be a set and let $B$ be a finite set carrying a probability law $\mu$, given by weights $\mu(c)\ge0$ with $\sum_{c\in B}\mu(c)=1$; for $P\subseteq B$ write $\mu(P)=\sum_{c\in P}\mu(c)$, and for $f:B\to\mathbb{R}$ write $\mathbb{E}_\mu[f]=\sum_{c\in B}\mu(c)f(c)$. Let $A=(A_c)_{c\in B}$ be a family of finite subsets of $X$ (a *weighted set family*: $c\sim\mu$ selects the random set $A_c$), and let $T\subseteq X$ be a finite *target* set.
--
--   **Theorem.** Let $m\in\mathbb{N}$ with $|T|\le m$, and let $g:\mathbb{N}\to\mathbb{R}$ be an arbitrary function. Then
--   $$
--   \mathbb{E}_\mu\bigl[c\mapsto g(|A_c\cap T|)\bigr]=\sum_{c\in B}\mu(c)\,g(|A_c\cap T|)\ =\ \sum_{r=0}^{m}\mu\bigl(\{c\in B:\ |A_c\cap T|=r\}\bigr)\,g(r).
--   $$
--
--   This is the law of the unconscious statistician for the intersection size $|A_c\cap T|$, which takes values in $\{0,1,\dots,m\}$; any a priori bound $m\ge|T|$ may be used as the summation range. It reduces moment estimates for $|A_c\cap T|$ to bounds on the point probabilities $\mu(|A_c\cap T|=r)$, which in turn are controlled by spread conditions.
--
--   **Formalization Note** The law is a `FiniteLaw B` with `Fintype B`, labels are `Finset X` for a type `X` with decidable equality, and $\mu(\cdot)$, $\mathbb{E}_\mu$ are `μ.prob` and `μ.expectation`. The label map need not be injective and individual weights may vanish. The range of summation is `Finset.range (m + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/SpreadCounting.lean#L107-L123

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem OAI.LeanBlast.SecondKahnKalai.expectation_intersection_eq_sum (μ : FiniteLaw B) (A : B → Finset X)
    {m : ℕ} {T : Finset X} (hT : T.card ≤ m) (g : ℕ → ℝ) :
    μ.expectation (fun c => g (A c ∩ T).card) =
      ∑ r ∈ Finset.range (m + 1),
        μ.prob (fun c => (A c ∩ T).card = r) * g r := by sorry
