-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectationThreshold_pos
-- name    : OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:38:34.586875+00:00
-- url     : https://prove2.me/theorems/8add8ad7-2c13-421c-b486-8d340e58de6c
-- title:
--   The expectation threshold of a graph with at least one edge is positive
-- statement:
--   Let $n$ be a natural number and let $H$ be a simple graph on a finite vertex set $V$ with $|V|\le n$ and with at least one edge (edges are unordered pairs, counted once).
--
--   For $p\in\mathbb{R}$, let $G(n,p)$ be the random graph on the vertex set $[n]=\{0,1,\dots,n-1\}$ in which each of the $\binom n2$ unordered pairs $\{i,j\}$ with $i\neq j$ is included independently with probability $p$; formally a set $W$ of such pairs has weight $p^{|W|}(1-p)^{\binom n2-|W|}$. For a graph $F$, let $X_F$ be the number of unlabelled non-induced copies of $F$ in $G(n,p)$, that is, the number of subgraphs of $G(n,p)$ isomorphic to $F$, and let $\mathbb E_p[X_F]$ be its expectation. The *expectation threshold* of $H$ is
--   $$q_E(n,H)=\inf\Big\{p\in[0,1]:\ \mathbb E_p[X_F]\ge\tfrac12\ \text{ for every subgraph }F\text{ of }H\Big\},$$
--   where $F$ ranges over all subgraphs of $H$ (a subset of the vertices of $H$ together with a subset of the edges of $H$ between them), each regarded as a graph on its own vertex set. The theorem states that
--   $$q_E(n,H)>0 .$$
--
--   Positivity of the expectation threshold is needed when the critical threshold of $H$ is compared with constant multiples of $q_E(n,H)$: in the main threshold bound of this development, a multiple of $q_E(n,H)$ serves as a strictly positive spread parameter.
--
--   **Formalization Note** The infimum is `sInf` on $\mathbb{R}$, which returns $0$ on the empty set; the hypothesis $|V|\le n$ makes $p=1$ admissible, so the admissible set is nonempty and the conclusion is not an artifact of that convention. The edge count is `edgeCount H = Nat.card H.edgeSet`, copies are counted by Mathlib's `SimpleGraph.copyCount`, and subgraphs are the elements of `H.Subgraph`, viewed as graphs via `F.coe`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Thresholds.lean#L167-L188

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators

theorem OAI.LeanBlast.SecondKahnKalai.expectationThreshold_pos {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n)
    (hedge : 1 ≤ edgeCount H) : 0 < expectationThreshold n H := by sorry
