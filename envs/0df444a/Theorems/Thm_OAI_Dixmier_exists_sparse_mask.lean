-- Prove2me | Theorems.Thm_OAI_Dixmier_exists_sparse_mask
-- name    : OAI.Dixmier.exists_sparse_mask
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:16:45.162622+00:00
-- url     : https://prove2.me/theorems/c66fd215-527e-424b-9a0e-b3df08b09cb5
-- title:
--   Sparse edge mask from a Hall density condition: at most $r$ ones per row and at most $r$ zeros per column
-- statement:
--   Let $G$ be a group, $I$ a finite set, $s=(s_i)_{i\in I}$ a family of elements of $G$ (repetitions allowed), and $r\in\mathbb{N}$. Consider the bipartite multigraph with edge set $G\times I$ in which the edge $(x,i)$ joins the row vertex $x$ to the column vertex $xs_i$ (rows and columns are two copies of $G$). Assume the density condition: for every finite set $F\subseteq G\times I$ of edges,
--   $$|F|\le r\Bigl(\bigl|\{x:(x,i)\in F\}\bigr|+\bigl|\{xs_i:(x,i)\in F\}\bigr|\Bigr).$$
--   Then there is a mask $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$ such that for all $x,y\in G$
--   $$\bigl|\{i\in I:\ a(x,i)=\mathrm{true}\}\bigr|\le r\qquad\text{and}\qquad\bigl|\{i\in I:\ a(ys_i^{-1},i)=\mathrm{false}\}\bigr|\le r.$$
--
--   The mask hands every edge either to its row endpoint (value true) or to its column endpoint (value false), in such a way that each row vertex $x$ keeps at most $r$ of its outgoing edges $(x,i)$ and each column vertex $y$ keeps at most $r$ of its incoming edges $(ys_i^{-1},i)$. Edge labels $i$ are kept separate even when products $s_i$ coincide, and $G$ may be uncountable. Such sparse splittings are the combinatorial input for building bounded masked convolution operators.
--
--   **Formalization Note** The mask is a function `a : G → I → Bool`; the two sets in the conclusion are `rowOnes a x` and `columnZeros a s y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean#L108-L139

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

open OAI OAI.Dixmier
open Finset
attribute [local instance] Classical.propDecidable
variable {E V W : Type*}

theorem OAI.Dixmier.exists_sparse_mask {G I : Type*} [Group G] [Fintype I] (s : I → G) (r : ℕ)
    (hdensity : ∀ F : Finset (G × I), F.card ≤
      r * ((F.image Prod.fst).card + (F.image (fun e => e.1 * s e.2)).card)) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by sorry
