-- Prove2me | Theorems.Thm_OAI_Dixmier_Masked_edge_summable
-- name    : OAI.Dixmier.Masked.edge_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:02.382517+00:00
-- url     : https://prove2.me/theorems/ef56bca1-e588-4384-bb1e-5964a395ae8d
-- title:
--   Masked edge energies along a fixed label are summable over the group
-- statement:
--   Let $G$ be a group, $K$ a finite set, and $\ell^2(G;\mathbb{C}^K)$ the Hilbert space of functions $\xi\colon G\to\mathbb{C}^K$ with $\sum_{x\in G}\|\xi(x)\|^2<\infty$. Let $I$ be an arbitrary index set, $(v_i)_{i\in I}$ vectors in $\mathbb{C}^K$, $s\colon I\to G$ a labelling, and $c\colon G\times I\to\mathbb{C}$ an arbitrary mask. Then for every $\xi\in\ell^2(G;\mathbb{C}^K)$ and every $i\in I$ the edge energies along label $i$ are summable over $G$:
--
--   $$\sum_{x\in G:\ c(x,i)\neq0}\big|\langle v_i,\xi(x s_i)\rangle\big|^2<\infty,$$
--
--   where $s_i=s(i)$.
--
--   For a masked operator $(A\xi)(x)=\sum_i c(x,i)\langle v_i,\xi(xs_i)\rangle v_i$, the quantity $\sum_{i:\,c(x,i)\neq0}|\langle v_i,\xi(xs_i)\rangle|^2$ is the edge energy at $x$. This lemma makes the series of edge energies over $G$ legitimate, so that they can be summed and reindexed in the proof of the masked operator bound.
--
--   **Formalization Note** The statement is `Summable` of the function of $x\in G$ equal to $|\langle v_i,\xi(xs_i)\rangle|^2$ when $c(x,i)\neq0$ and to $0$ otherwise; for nonnegative terms this is finiteness of the sum. The space is the Mathlib `lp` space of $\mathbb{C}^K$-valued functions on $G$ with exponent $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Masked.lean#L55-L70

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

omit [Fintype I] in
theorem OAI.Dixmier.Masked.edge_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (i : I) :
    Summable (fun x => if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) := by sorry
