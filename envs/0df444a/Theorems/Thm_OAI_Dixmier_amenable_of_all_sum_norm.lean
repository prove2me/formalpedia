-- Prove2me | Theorems.Thm_OAI_Dixmier_amenable_of_all_sum_norm
-- name    : OAI.Dixmier.amenable_of_all_sum_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:38.5393+00:00
-- url     : https://prove2.me/theorems/17901b74-34b4-4dd6-8849-3df7e9f1b19a
-- title:
--   If $\|\sum_{g\in S}R_g\|=|S|$ for every finite $S$ containing $1$, then $G$ is amenable
-- statement:
--   Let $G$ be a group with the discrete topology and let $R$ be its right regular representation on the Hilbert space $\ell^2(G)$ of square-summable functions $G\to\mathbb{C}$, $(R_g\xi)(x)=\xi(xg)$. Suppose that for every finite set $S\subseteq G$ with $1\in S$,
--   $$\Bigl\|\sum_{g\in S}R_g\Bigr\|=|S|.$$
--   Then $G$ is amenable: writing $\ell^\infty(G)$ for the bounded functions $G\to\mathbb{C}$, $\mathbf 1$ for the constant function $1$ and $(\lambda_gb)(x)=b(g^{-1}x)$ for left translation, there is a $\mathbb{C}$-linear functional $M$ on $\ell^\infty(G)$ with $M(\mathbf 1)=1$, such that $M(b)$ is a nonnegative real number whenever every value $b(x)$ is a nonnegative real number, and such that $M(\lambda_gb)=M(b)$ for all $g\in G$ and $b\in\ell^\infty(G)$.
--
--   Since each $R_g$ is an isometry, $|S|$ is always an upper bound for the norm of the sum, so the hypothesis says that this trivial bound is attained for every finite $S$ containing the identity. The contrapositive is the form used later: a nonamenable group has a finite set $S\ni1$ whose sum of right translations has norm strictly smaller than $|S|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Contracting.lean#L30-L52

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

open OAI OAI.Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem OAI.Dixmier.amenable_of_all_sum_norm
    (h : ∀ S : Finset G, 1 ∈ S → ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ)) :
    Amenable G := by sorry
