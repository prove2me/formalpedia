-- Prove2me | Theorems.Thm_OAI_Dixmier_SphereNet_operator_norm_le_ten
-- name    : OAI.Dixmier.SphereNet.operator_norm_le_ten
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:44.640964+00:00
-- url     : https://prove2.me/theorems/a951e9bb-d405-496b-aba5-30169c2bd05f
-- title:
--   Quarter-net bilinear tests bounded by 5 give operator norm at most 10
-- statement:
--   Let $E$ and $F$ be real inner product spaces and let $M\colon E\to F$ be a continuous linear map with operator norm $\|M\|$. Let $s\subseteq E$ and $t\subseteq F$ be finite sets of unit vectors that are $\tfrac14$-nets of the respective unit spheres: for every unit vector $x\in E$ there is $x_0\in s$ with $\|x-x_0\|\le\tfrac14$, and for every unit vector $y\in F$ there is $y_0\in t$ with $\|y-y_0\|\le\tfrac14$. If the bilinear form of $M$ is bounded by $5$ on all pairs of net points,
--
--   $$|\langle Mx_0,y_0\rangle|\le 5\qquad\text{for all }x_0\in s,\ y_0\in t,$$
--
--   then
--
--   $$\|M\|\le 10.$$
--
--   This is the standard net argument that reduces an operator-norm bound to finitely many bilinear tests. It is what allows a union bound over two finite nets to control the norms of random sign-matrix synthesis operators.
--
--   **Formalization Note** Neither space is assumed complete or finite-dimensional (the existence of finite nets of the unit spheres forces finite dimension). The hypothesis that the points of $s$ are unit vectors is part of the statement, although the argument only uses that the points of $t$ are unit vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/NetOperator.lean#L14-L47

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

open OAI OAI.Dixmier
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem OAI.Dixmier.SphereNet.operator_norm_le_ten (M : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (_hs : ∀ x ∈ s, ‖x‖ = 1) (ht : ∀ y ∈ t, ‖y‖ = 1)
    (hsnet : ∀ x : E, ‖x‖ = 1 → ∃ x₀ ∈ s, ‖x-x₀‖ ≤ (1/4 : ℝ))
    (htnet : ∀ y : F, ‖y‖ = 1 → ∃ y₀ ∈ t, ‖y-y₀‖ ≤ (1/4 : ℝ))
    (hM : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (M x) y| ≤ 5) : ‖M‖ ≤ 10 := by sorry
