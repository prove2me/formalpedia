-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliProbability_subset
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:57.281319+00:00
-- url     : https://prove2.me/theorems/dbefce2b-879f-41fa-88ca-6c18b874ab9b
-- title:
--   A fixed set $A$ lies in a $p$-random subset with probability $p^{|A|}$
-- statement:
--   Let $X$ be a finite set and $p\in\mathbb{R}$. Give each subset $W\subseteq X$ the weight
--   $$
--   w_p(W)=\prod_{x\in W}p\prod_{x\in X\setminus W}(1-p)=p^{|W|}(1-p)^{|X|-|W|},
--   $$
--   and for a property $P$ of subsets of $X$ put $\mathbb{P}_p[P]=\sum_{W\subseteq X,\ P(W)}w_p(W)$. When $0\le p\le 1$, $w_p$ is the distribution of the random subset of $X$ that contains each element independently with probability $p$, and $\mathbb{P}_p[P]$ is the probability that this random subset has property $P$.
--
--   **Theorem.** For every real number $p$ and every subset $A\subseteq X$,
--   $$
--   \mathbb{P}_p[A\subseteq W]=\sum_{W\,:\,A\subseteq W\subseteq X}w_p(W)=p^{|A|}.
--   $$
--
--   In probabilistic language: a fixed set $A$ survives in the $p$-random subset with probability $p^{|A|}$. This is the basic computation behind first-moment estimates for random graphs: applied to the edge set of a fixed subgraph of the complete graph $K_n$, it says that all $e$ edges of that subgraph are present in $G(n,p)$ with probability $p^{e}$.
--
--   **Formalization Note** The identity is proved for every real $p$, not only for $p\in[0,1]$ (both sides are polynomials in $p$). The weight is `bernoulliWeight p W`, defined as the product over $x\in X$ of `if x ∈ W then p else 1 - p`, and $\mathbb{P}_p$ is `bernoulliProbability p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/FiniteProbability.lean#L238-L267

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset (p : ℝ) (A : Finset X) :
    bernoulliProbability p (fun W => A ⊆ W) = p ^ A.card := by sorry
