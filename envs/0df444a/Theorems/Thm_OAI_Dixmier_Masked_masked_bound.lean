-- Prove2me | Theorems.Thm_OAI_Dixmier_Masked_masked_bound
-- name    : OAI.Dixmier.Masked.masked_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:21.49063+00:00
-- url     : https://prove2.me/theorems/725af0e3-6def-4e69-9ea7-2886d7c96313
-- title:
--   Row and column synthesis bounds give the masked operator bound $b^2$
-- statement:
--   Let $G$ be a group, $I$ and $K$ finite sets, and $\ell^2(G;\mathbb{C}^K)$ the Hilbert space of square-summable functions $\xi\colon G\to\mathbb{C}^K$. Let $v_i\in\mathbb{C}^K$ ($i\in I$) be vectors, $s\colon I\to G$ a labelling with $s_i=s(i)$ (not necessarily injective), and $c\colon G\times I\to\mathbb{C}$ a mask with $|c(x,i)|\le1$ for all $x,i$. The masked operator $A$ on $\ell^2(G;\mathbb{C}^K)$ is
--
--   $$(A\xi)(x)=\sum_{i\in I}c(x,i)\,\langle v_i,\xi(xs_i)\rangle\,v_i\qquad(x\in G),$$
--
--   with the inner product conjugate-linear in its first argument, so that $\langle v_i,w\rangle v_i=v_iv_i^*w$. For $J\subseteq I$ let $T_J\colon\mathbb{C}^J\to\mathbb{C}^K$, $T_Jz=\sum_{i\in J}z_iv_i$, be the synthesis operator, and define the row and column supports
--
--   $$R(x)=\{i\in I:\ c(x,i)\neq0\},\qquad C(y)=\{i\in I:\ c(ys_i^{-1},i)\neq0\}.$$
--
--   Let $b\ge0$. If $\|T_{R(x)}\|\le b$ for every $x\in G$ and $\|T_{C(y)}\|\le b$ for every $y\in G$, then
--
--   $$\|A\|\le b^2 .$$
--
--   This is a Schur-test type estimate in which row and column sums are replaced by synthesis norms of the active subfamilies: $i\in R(x)$ means that the edge from $x$ to $xs_i$ is active, and $i\in C(y)$ means that the edge arriving at $y$ along label $i$ is active. It converts frame bounds for small subfamilies into uniform operator bounds for masked operators.
--
--   **Formalization Note** The operator is `Masked.operator v s c hc`, a finite sum over $i$ of the operators $\xi\mapsto\big(x\mapsto c(x,i)\,v_iv_i^*\,\xi(xs_i)\big)$; $R(x)$ and $C(y)$ are `rowSet c x` and `columnSet s c y`. The vectors $v_i$ are not required to be unit vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Masked.lean#L133-L159

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
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked

open OAI OAI.Dixmier OAI.Dixmier.Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
private noncomputable local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_1 : DecidableEq G := Classical.decEq G
attribute [local instance] OAI.Dixmier.Masked.instDecidableEqComplex_oAI

theorem OAI.Dixmier.Masked.masked_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (hcol : ∀ y, ‖FiniteSynthesis.synthesis v (columnSet s c y)‖ ≤ b) :
    ‖operator v s c hc‖ ≤ b^2 := by sorry
