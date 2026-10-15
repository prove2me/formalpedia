-- Prove2me | Theorems.Thm_OAI_Dixmier_exists_contracting_sum
-- name    : OAI.Dixmier.exists_contracting_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:56.556527+00:00
-- url     : https://prove2.me/theorems/9577a12c-9e15-45e5-b44d-ff141df8b6d8
-- title:
--   A nonamenable group has a finite set $S\ni 1$ with $|S|\ge2$ and $\|\sum_{g\in S}R_g\|\le\rho\,|S|$ for some $\rho<1$
-- statement:
--   Let $G$ be a group with the discrete topology that is not amenable, i.e. there is no $\mathbb{C}$-linear functional $m$ on the bounded functions $G\to\mathbb{C}$ with $m(\mathbf 1)=1$, $m(b)$ a nonnegative real number whenever all values of $b$ are nonnegative real numbers, and $m(\lambda_gb)=m(b)$ for all $g\in G$, where $(\lambda_gb)(x)=b(g^{-1}x)$. Let $R$ be the right regular representation of $G$ on $\ell^2(G)$, $(R_g\xi)(x)=\xi(xg)$. Then there exist a finite set $S\subseteq G$ with $1\in S$ and $|S|\ge2$, and a real number $\rho$ with $0<\rho<1$, such that
--   $$\Bigl\|\sum_{g\in S}R_g\Bigr\|\le|S|\,\rho.$$
--
--   Equivalently, the averaging operator $\frac{1}{|S|}\sum_{g\in S}R_g$ has norm at most $\rho<1$. This quantitative form of nonamenability is exactly the hypothesis of the sparse-splitting theorem for words, applied with the index set $I=S$ and $s_g=g$; there the bounds $\lceil|S|^\ell\rho^\ell\rceil$ are exponentially small compared with the number $|S|^\ell$ of words of length $\ell$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Contracting.lean#L54-L77

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

theorem OAI.Dixmier.exists_contracting_sum (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) * ρ := by sorry
