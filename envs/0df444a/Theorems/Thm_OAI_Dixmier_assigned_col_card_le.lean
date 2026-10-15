-- Prove2me | Theorems.Thm_OAI_Dixmier_assigned_col_card_le
-- name    : OAI.Dixmier.assigned_col_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:16:30.28562+00:00
-- url     : https://prove2.me/theorems/8cff3034-5805-49c4-ae35-53a07bf42a23
-- title:
--   An injective endpoint-slot assignment puts at most $r$ edges into the column slots of a vertex
-- statement:
--   Let $E$, $V$, $W$ be arbitrary sets and let $r\in\mathbb{N}$. Think of $E$ as the set of edge labels of a bipartite multigraph: the edge $e$ joins the row vertex $\operatorname{row}(e)\in V$ to the column vertex $\operatorname{col}(e)\in W$. Every vertex has $r$ slots, numbered by $[r]=\{0,1,\dots,r-1\}$, so the set of all slots is the disjoint union
--   $$\Sigma=(V\times[r])\sqcup(W\times[r]),$$
--   whose elements of the first kind are *row slots* and those of the second kind *column slots*. The endpoint slots of an edge $e$ are the $2r$ slots at its two endpoints,
--   $$\Sigma(e)=\bigl(\{\operatorname{row}(e)\}\times[r]\bigr)\sqcup\bigl(\{\operatorname{col}(e)\}\times[r]\bigr).$$
--
--   Let $f:E\to\Sigma$ be injective with $f(e)\in\Sigma(e)$ for every $e\in E$. Then for every column vertex $w\in W$ and every finite set $F\subseteq E$ such that each $e\in F$ satisfies $\operatorname{col}(e)=w$ and $f(e)$ is a column slot,
--   $$|F|\le r.$$
--
--   This is the column counterpart of the row-slot bound: an injective assignment of edges to slots at their own endpoints sends at most $r$ edges into the $r$ column slots of any single column vertex. Both bounds together turn an assignment produced by Hall's theorem into a splitting of the edges with at most $r$ edges kept at every vertex.
--
--   **Formalization Note** Slots are elements of the sum type `(V × Fin r) ⊕ (W × Fin r)`; $\Sigma(e)$ is `endpointSlots row col r e`, and "$f(e)$ is a column slot" is `isRowSlot (f e) = false`. No finiteness or countability is assumed on $E$, $V$ or $W$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean#L90-L106

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

theorem OAI.Dixmier.assigned_col_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (w : W) (F : Finset E) (hF : ∀ e ∈ F, col e = w ∧ isRowSlot (f e) = false) :
    F.card ≤ r := by sorry
