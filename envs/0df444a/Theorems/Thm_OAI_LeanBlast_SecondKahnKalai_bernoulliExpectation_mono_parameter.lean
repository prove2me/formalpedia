-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_mono_parameter
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:56:45.239145+00:00
-- url     : https://prove2.me/theorems/7001ee09-6f44-4d7f-87a0-da6a49f8d977
-- title:
--   Bernoulli expectations of increasing set functions are monotone in the parameter
-- statement:
--   Let $X$ be a finite set. For a real number $p$ and a subset $W\subseteq X$ put $w_p(W)=\prod_{x\in X}\bigl(p\ \text{if } x\in W,\ \text{else } 1-p\bigr)$, i.e. $w_p(W)=p^{|W|}(1-p)^{|X|-|W|}$ (with $0^0=1$), and for a function $F:2^X\to\mathbb{R}$ on subsets of $X$ define the *Bernoulli expectation* $\mathbb{E}_p[F]=\sum_{W\subseteq X}w_p(W)\,F(W)$. When $0\le p\le 1$, $w_p$ is the law of the $p$-random subset $X_p$ of $X$, which contains each element independently with probability $p$, and $\mathbb{E}_p[F]$ is the expectation of $F(X_p)$.
--
--   A function $F:2^X\to\mathbb{R}$ is *increasing* if $U\subseteq V$ implies $F(U)\le F(V)$.
--
--   **Theorem.** If $0\le p\le q\le 1$ and $F$ is increasing, then
--   $$
--   \mathbb{E}_p[F]\le\mathbb{E}_q[F].
--   $$
--
--   The function $F$ need not be nonnegative, and both endpoints $p=0$ and $q=1$ are allowed. Applied to the indicator of an up-closed family of subsets, it gives the familiar fact that the probability of a monotone increasing property of the random set $X_p$ is nondecreasing in $p$; this is used to compare covering probabilities at different sampling parameters.
--
--   **Formalization Note** Subsets are `Finset X` for a `Fintype X` with decidable equality, and $\mathbb{E}_p$ is `bernoulliExpectation p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/BernoulliMonotonicity.lean#L20-L50

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (F : Finset X → ℝ)
    (hF : ∀ U V, U ⊆ V → F U ≤ F V) :
    bernoulliExpectation p F ≤ bernoulliExpectation q F := by sorry
