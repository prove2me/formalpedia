-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_intersection_truncated_moment_le
-- name    : OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:04:20.281592+00:00
-- url     : https://prove2.me/theorems/dc11a2ed-2bb2-479e-9c4f-4f6ae6c42dcb
-- title:
--   Truncated moment bound for the intersection of an $a$-spread family with a set of size at most $m$
-- statement:
--   Let $X$ be a set and let $B$ be a finite set carrying a probability law $\mu$, given by weights $\mu(c)\ge0$ with $\sum_{c\in B}\mu(c)=1$; for $P\subseteq B$ write $\mu(P)=\sum_{c\in P}\mu(c)$, and for $f:B\to\mathbb{R}$ write $\mathbb{E}_\mu[f]=\sum_{c\in B}\mu(c)f(c)$. Let $A=(A_c)_{c\in B}$ be a family of finite subsets of $X$ (a *weighted set family*: $c\sim\mu$ selects the random set $A_c$), and let $T\subseteq X$ be a finite *target* set. The family is *$a$-spread* for a real $a$ if $\mu(\{c\in B: J\subseteq A_c\})\le a^{|J|}$ for every nonempty finite $J\subseteq X$.
--
--   **Theorem.** Let $a\ge0$ and suppose the family $(\mu,A)$ is $a$-spread. Let $m\in\mathbb{N}$ with $|T|\le m$, let $t\ge 0$, and let $Q$ be any predicate on $\mathbb{N}$. Then
--   $$
--   \sum_{c\in B}\mu(c)\,\mathbf 1\bigl[Q(|A_c\cap T|)\bigr]\,t^{|A_c\cap T|}\ \le\ \sum_{r=0}^{m}\mathbf 1[Q(r)]\binom{m}{r}(a\,t)^{r}.
--   $$
--
--   With $Q$ always true, this is the generating-function bound $\mathbb{E}_\mu\bigl[t^{|A_c\cap T|}\bigr]\le(1+at)^m$; the predicate allows one to keep only part of the distribution, for instance the large intersections $|A_c\cap T|>k$, which is how tail contributions are estimated (for example with $t=1/\rho$ in the analysis of a resampling step). The convention $t^0=1$ is used, also for $t=0$.
--
--   **Formalization Note** The law is a `FiniteLaw B` with `Fintype B`, labels are `Finset X` for a type `X` with decidable equality, and $\mu(\cdot)$, $\mathbb{E}_\mu$ are `μ.prob` and `μ.expectation`. The label map need not be injective and individual weights may vanish. The spread hypothesis is `IsSpread μ A a`, the predicate `Q : ℕ → Prop` is decidable, and the left-hand side is `μ.expectation (fun c => if Q (A c ∩ T).card then t ^ (A c ∩ T).card else 0)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/SpreadCounting.lean#L135-L153

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

theorem OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (Q : ℕ → Prop) [DecidablePred Q] :
    μ.expectation (fun c => if Q (A c ∩ T).card then t ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a * t) ^ r else 0 := by sorry
