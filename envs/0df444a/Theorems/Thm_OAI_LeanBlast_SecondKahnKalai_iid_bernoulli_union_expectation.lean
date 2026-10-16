-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_iid_bernoulli_union_expectation
-- name    : OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:55:47.338308+00:00
-- url     : https://prove2.me/theorems/c69964d0-9a57-40f0-9346-3483c96a88a0
-- title:
--   The union of $n$ independent $p$-random subsets is a $(1-(1-p)^n)$-random subset
-- statement:
--   Let $X$ be a finite set. For a real number $p$ and a subset $W\subseteq X$ put $w_p(W)=\prod_{x\in X}\bigl(p\ \text{if } x\in W,\ \text{else } 1-p\bigr)$, i.e. $w_p(W)=p^{|W|}(1-p)^{|X|-|W|}$ (with $0^0=1$), and for a function $F:2^X\to\mathbb{R}$ on subsets of $X$ define the *Bernoulli expectation* $\mathbb{E}_p[F]=\sum_{W\subseteq X}w_p(W)\,F(W)$. When $0\le p\le 1$, $w_p$ is the law of the $p$-random subset $X_p$ of $X$, which contains each element independently with probability $p$, and $\mathbb{E}_p[F]$ is the expectation of $F(X_p)$.
--
--   For $0\le p\le1$ let $\nu_p$ denote the law $w_p$ on subsets of $X$, and let $\nu_p^{\otimes n}$ be the law of an $n$-tuple $(W_1,\dots,W_n)$ of independent $p$-random subsets, with weight $\prod_{i=1}^n w_p(W_i)$.
--
--   **Theorem.** Let $0\le p\le 1$, $n\in\mathbb{N}$ and $F:2^X\to\mathbb{R}$. Then
--   $$
--   \sum_{(W_1,\dots,W_n)}\Bigl(\prod_{i=1}^{n}w_p(W_i)\Bigr)\,F\bigl(W_1\cup\dots\cup W_n\bigr)=\mathbb{E}_{1-(1-p)^n}[F],
--   $$
--   the sum running over all $n$-tuples of subsets of $X$. For $n=0$ the union is empty and both sides equal $F(\emptyset)$.
--
--   Thus the union of $n$ independent rounds of $p$-sampling is exactly a single random subset with parameter $1-(1-p)^n$, a parameter that is at most $np$. In threshold arguments this converts the success probability of a procedure that reveals several independent random sets into a statement about one Bernoulli random set.
--
--   **Formalization Note** The law $\nu_p$ is `bernoulliLaw p hp0 hp1`, a `FiniteLaw (Finset X)`, the product law is `.iid n` on `Fin n → Finset X`, the union is `Finset.univ.biUnion draws`, and the right-hand side is `bernoulliExpectation (1 - (1 - p) ^ n) F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/BernoulliUnion.lean#L98-L117

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
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.LeanBlast.SecondKahnKalai.iid_bernoulli_union_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (F : Finset X → ℝ) :
    ((bernoulliLaw p hp0 hp1).iid n).expectation (fun draws => F (Finset.univ.biUnion draws)) =
      bernoulliExpectation (1 - (1 - p) ^ n) F := by sorry
