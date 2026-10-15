-- Prove2me | Theorems.Thm_OAI_Dixmier_almost_invariant_of_sum_norm
-- name    : OAI.Dixmier.almost_invariant_of_sum_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:47.064388+00:00
-- url     : https://prove2.me/theorems/1c62e048-9e5f-40e5-930c-ea5da3122fd7
-- title:
--   If $\|\sum_{g\in S}R_g\|=|S|$, then $\ell^2(G)$ has unit vectors almost invariant under right translation by $S$
-- statement:
--   Let $G$ be a group and let $R$ be its right regular representation on the Hilbert space $\ell^2(G)$ of square-summable functions $G\to\mathbb{C}$, $(R_g\xi)(x)=\xi(xg)$. Let $S\subseteq G$ be a finite set containing the identity $1$, and assume that the sum of the right translations by elements of $S$ has norm exactly $|S|$:
--   $$\Bigl\|\sum_{g\in S}R_g\Bigr\|=|S|.$$
--   Then for every $\varepsilon>0$ there is a vector $\xi\in\ell^2(G)$ with $\|\xi\|=1$ such that
--   $$\|R_g\xi-\xi\|<\varepsilon\qquad\text{for all }g\in S.$$
--
--   Since each $R_g$ is an isometry, $|S|$ is the trivial upper bound for the norm of the sum, and the theorem says that attaining it forces the existence of unit vectors that are almost invariant under every translation in $S$. Such vectors are converted into approximately invariant means, which is how a norm condition on the regular representation leads to amenability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Average.lean#L56-L82

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

open OAI OAI.Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : Type*} [Group G]

theorem OAI.Dixmier.almost_invariant_of_sum_norm (S : Finset G) (h1 : (1 : G) ∈ S)
    (hS : ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ScalarL2 G, ‖ξ‖ = 1 ∧ ∀ g ∈ S, ‖rightRegular g ξ - ξ‖ < ε := by sorry
