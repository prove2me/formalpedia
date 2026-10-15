-- Prove2me | Theorems.Thm_OAI_Dixmier_endpoint_density_of_rectangle_bound
-- name    : OAI.Dixmier.endpoint_density_of_rectangle_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:17:54.264981+00:00
-- url     : https://prove2.me/theorems/542ae32a-02d7-40a0-9874-e121bf23f742
-- title:
--   Rectangle edge bounds imply the Hall density condition $|F|\le r\,(|\pi_1F|+|\pi_2F|)$
-- statement:
--   Let $G$ be a group, $I$ a finite set and $s=(s_i)_{i\in I}$ a family of elements of $G$; for finite $U,V\subseteq G$ let $E(U,V)=\{(x,i)\in U\times I:\ xs_i\in V\}$. Let $q\in\mathbb{R}$ and $r\in\mathbb{N}$ satisfy $0\le q\le r$, and assume that for all finite $U,V\subseteq G$
--   $$|E(U,V)|\le q\sqrt{|U|\,|V|}.$$
--   Then every finite set $F\subseteq G\times I$ satisfies
--   $$|F|\le r\,\bigl(|\pi_1(F)|+|\pi_2(F)|\bigr),\qquad\text{where}\quad \pi_1(F)=\{x:(x,i)\in F\},\quad \pi_2(F)=\{xs_i:(x,i)\in F\}.$$
--
--   The conclusion is exactly the Hall-type density condition needed to split the edges $(x,i)$, each joining $x$ to $xs_i$, into a part with at most $r$ edges at each row vertex and a part with at most $r$ edges at each column vertex. Combined with the rectangle estimate for convolution operators, it converts a norm bound $\bigl\|\sum_iR_{s_i}\bigr\|\le r$ into such a sparse splitting.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseSplitting.lean#L91-L110

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

theorem OAI.Dixmier.endpoint_density_of_rectangle_bound (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by sorry
