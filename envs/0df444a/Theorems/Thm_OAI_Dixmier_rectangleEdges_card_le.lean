-- Prove2me | Theorems.Thm_OAI_Dixmier_rectangleEdges_card_le
-- name    : OAI.Dixmier.rectangleEdges_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:17:39.739856+00:00
-- url     : https://prove2.me/theorems/7124d369-c7fc-4c45-a975-bb703a0f28f3
-- title:
--   A norm bound on a convolution operator bounds labelled edges between finite sets by $q\sqrt{|U|\,|V|}$
-- statement:
--   Let $G$ be a group, $I$ a finite set and $s=(s_i)_{i\in I}$ a family of elements of $G$. Let $\ell^2(G)$ be the Hilbert space of square-summable functions $G\to\mathbb{C}$, and let $A$ be a bounded linear operator on $\ell^2(G)$ acting by
--   $$(A\xi)(x)=\sum_{i\in I}\xi(xs_i)\qquad(\xi\in\ell^2(G),\ x\in G),$$
--   so that $A=\sum_{i\in I}R_{s_i}$ is a sum of right translations $(R_t\xi)(x)=\xi(xt)$. For finite sets $U,V\subseteq G$ let
--   $$E(U,V)=\bigl\{(x,i)\in U\times I:\ xs_i\in V\bigr\}$$
--   be the set of labelled edges from $U$ to $V$. If $q\in\mathbb{R}$ satisfies $\|A\|\le q$, then for all finite $U,V\subseteq G$
--   $$|E(U,V)|\le q\,\sqrt{|U|\,|V|}.$$
--
--   Edges are counted with their labels, so coinciding values $s_i=s_{i'}$ contribute separately. This is the spectral input of the sparse-splitting argument: a norm bound on the convolution operator forces every finite rectangle $U\times V$ to contain few edges, which in turn yields Hall's density condition.
--
--   **Formalization Note** $\ell^2(G)$ is `ScalarL2 G`, the `lp` space of complex functions on $G$ with exponent 2, and $E(U,V)$ is the finset `rectangleEdges s U V` of $G\times I$. The operator $A$ enters only through the coefficient formula hypothesis `hA`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseSplitting.lean#L57-L74

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting

open OAI OAI.Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]
variable [Group G]

theorem OAI.Dixmier.rectangleEdges_card_le (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {q : ℝ} (hq : ‖A‖ ≤ q) (U V : Finset G) :
    ((rectangleEdges s U V).card : ℝ) ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := by sorry
