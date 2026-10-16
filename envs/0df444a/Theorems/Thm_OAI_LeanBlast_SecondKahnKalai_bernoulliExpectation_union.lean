-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_union
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:54:23.090732+00:00
-- url     : https://prove2.me/theorems/95a7f3bb-a89a-4782-a5e1-1d750782c0d5
-- title:
--   The union of independent $p$- and $q$-random subsets is a $(p+q-pq)$-random subset
-- statement:
--   Let $X$ be a finite set. For a real number $p$ and a subset $W\subseteq X$ put $w_p(W)=\prod_{x\in X}\bigl(p\ \text{if } x\in W,\ \text{else } 1-p\bigr)$, i.e. $w_p(W)=p^{|W|}(1-p)^{|X|-|W|}$ (with $0^0=1$), and for a function $F:2^X\to\mathbb{R}$ on subsets of $X$ define the *Bernoulli expectation* $\mathbb{E}_p[F]=\sum_{W\subseteq X}w_p(W)\,F(W)$. When $0\le p\le 1$, $w_p$ is the law of the $p$-random subset $X_p$ of $X$, which contains each element independently with probability $p$, and $\mathbb{E}_p[F]$ is the expectation of $F(X_p)$.
--
--   **Theorem.** For all real numbers $p,q$ and every function $F:2^X\to\mathbb{R}$,
--   $$
--   \mathbb{E}_p\Bigl[U\mapsto \mathbb{E}_q\bigl[V\mapsto F(U\cup V)\bigr]\Bigr]=\mathbb{E}_{p+q-pq}[F].
--   $$
--
--   For $p,q\in[0,1]$ this says that if $X_p$ and $X_q$ are independent random subsets, then $X_p\cup X_q$ has the same law as $X_{p+q-pq}$: an element is missed by the union with probability $(1-p)(1-q)=1-(p+q-pq)$, independently of the other elements. The identity is the basic tool for computing the law of the union of several independent rounds of sampling, and for coupling Bernoulli random sets with different parameters (monotonicity in the parameter).
--
--   **Formalization Note** The identity is algebraic and holds for all real $p$ and $q$; no restriction to $[0,1]$ is assumed. Subsets are `Finset X` for a `Fintype X` with decidable equality, and $w_p$, $\mathbb{E}_p$ are `bernoulliWeight p` and `bernoulliExpectation p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/BernoulliUnion.lean#L58-L79

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

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_union (p q : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun U => bernoulliExpectation q (fun V => F (U ∪ V))) =
      bernoulliExpectation (p + q - p * q) F := by sorry
