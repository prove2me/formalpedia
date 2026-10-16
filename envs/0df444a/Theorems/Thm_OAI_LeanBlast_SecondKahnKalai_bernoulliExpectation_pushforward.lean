-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_pushforward
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:50:12.599984+00:00
-- url     : https://prove2.me/theorems/73487a64-fced-48e2-87c4-cacced581ba3
-- title:
--   Change of variables for expectations over a $p$-random subset
-- statement:
--   Let $X$ be a finite set and $p\in\mathbb{R}$. Write $2^{X}$ for the family of all subsets of $X$, give $W\in 2^{X}$ the weight $w_p(W)=p^{|W|}(1-p)^{|X|-|W|}$, and for $f:2^{X}\to\mathbb{R}$ put $\mathbb{E}_p[f(W)]=\sum_{W\subseteq X}w_p(W)f(W)$. For $0\le p\le 1$ this is the expectation over the random subset of $X$ that contains each element independently with probability $p$.
--
--   **Theorem.** For every map $T:2^{X}\to 2^{X}$ and every function $F:2^{X}\to\mathbb{R}$,
--   $$
--   \mathbb{E}_p\bigl[F(T(W))\bigr]=\sum_{Y\subseteq X}\mathbb{E}_p\bigl[\mathbf{1}[T(W)=Y]\bigr]\,F(Y).
--   $$
--
--   For $0\le p\le 1$ the coefficient $\mathbb{E}_p[\mathbf{1}[T(W)=Y]]$ is the probability that the transformed random set $T(W)$ equals $Y$, so this is the change-of-variables (pushforward) formula $\mathbb{E}[F(T(W))]=\sum_{Y}\mathbb{P}[T(W)=Y]\,F(Y)$. It is used to compute with the laws of transformed random sets, for instance $U\cup W$ for a fixed set $U$, in the coupling arguments of the threshold proof.
--
--   **Formalization Note** The identity holds for every real $p$; the expectation is `bernoulliExpectation p`, and the indicator is written `if T W = Y then 1 else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/BernoulliCoupling.lean#L55-L69

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward (p : ℝ) (T : Finset X → Finset X)
    (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (T W)) =
      ∑ Y : Finset X, bernoulliExpectation p (fun W => if T W = Y then 1 else 0) * F Y := by sorry
