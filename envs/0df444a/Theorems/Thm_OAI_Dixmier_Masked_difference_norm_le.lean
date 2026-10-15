-- Prove2me | Theorems.Thm_OAI_Dixmier_Masked_difference_norm_le
-- name    : OAI.Dixmier.Masked.difference_norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:47.861543+00:00
-- url     : https://prove2.me/theorems/c75941a4-13e3-461b-8831-95ffb52f699e
-- title:
--   Sparse 0/1 masks give coboundaries of norm at most $b^2$ for the left regular representation
-- statement:
--   Let $G$ be a group, $I$ a finite set with $n=|I|$ elements, $K$ a finite set, and let $\lambda$ be the left regular representation of $G$ on $\ell^2(G;\mathbb{C}^K)$, given by $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$. Let $v_i\in\mathbb{C}^K$ ($i\in I$), a labelling $s\colon I\to G$ with $s_i=s(i)$, and a mask $a\colon G\times I\to\{0,1\}$ be given. The oriented operator $A_a$ is the masked operator
--
--   $$(A_a\xi)(x)=\sum_{i\in I}a(x,i)\,\langle v_i,\xi(xs_i)\rangle\,v_i\qquad(x\in G),$$
--
--   with the inner product conjugate-linear in its first argument. Fix $r\in\mathbb{N}$ and $b\ge0$, and assume:
--
--   1. (frame bound) for every $J\subseteq I$ with $|J|\le\min(2r,n)$, the synthesis operator $T_J\colon\mathbb{C}^J\to\mathbb{C}^K$, $T_Jz=\sum_{i\in J}z_iv_i$, satisfies $\|T_J\|\le b$;
--   2. (sparse rows) for every $x\in G$, at most $r$ indices $i$ have $a(x,i)=1$;
--   3. (sparse column zeros) for every $y\in G$, at most $r$ indices $i$ have $a(ys_i^{-1},i)=0$.
--
--   Then for every $g\in G$,
--
--   $$\big\|A_a-\lambda(g)\,A_a\,\lambda(g)^{-1}\big\|\le b^2 .$$
--
--   Thus $g\mapsto A_a-\lambda(g)A_a\lambda(g)^{-1}$ is a uniformly bounded coboundary for the left regular representation, even though no bound on $\|A_a\|$ itself is asserted. In the construction of uniformly bounded non-unitarizable representations of nonamenable groups, these coboundaries (one for each stage, built from frames and sparse masks) are summed directly to form the bounded cocycle of the upper triangular representation.
--
--   **Formalization Note** $A_a$ is `Masked.oriented v s a`, the masked operator with complex mask `boolComplex (a x i)` (equal to $1$ for `true` and $0$ for `false`); the left-hand side is `coboundary KernelObstruction.translation (oriented v s a) g`, i.e. $A_a-\lambda(g)A_a\lambda(g^{-1})$. Assumption 1 is `FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean#L100-L118

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
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra

open OAI OAI.Dixmier OAI.Dixmier.Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
private noncomputable local instance instDecidableEq_oAI_2 : DecidableEq I := Classical.decEq I
attribute [local instance] OAI.Dixmier.Masked.instDecidableEq_oAI_3
private noncomputable local instance instDecidableEqComplex_oAI_1 : DecidableEq ℂ := Classical.decEq ℂ

theorem OAI.Dixmier.Masked.difference_norm_le (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (hc : ∀ y, (columnZeros a s y).card ≤ r) (g : G) :
    ‖coboundary KernelObstruction.translation (oriented v s a) g‖ ≤ b^2 := by sorry
