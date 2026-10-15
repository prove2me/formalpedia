-- Prove2me | Theorems.Thm_OAI_Dixmier_l2_square_difference_bound
-- name    : OAI.Dixmier.l2_square_difference_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:58.57128+00:00
-- url     : https://prove2.me/theorems/0e07f2bf-63fc-45af-9cf0-d0781e91de41
-- title:
--   An $\ell^2$-to-$\ell^1$ bound for differences of squared moduli
-- statement:
--   Let $G$ be any set and let $\xi,\eta\in\ell^2(G)$ be square-summable functions $G\to\mathbb{C}$, with $\|\cdot\|_2$ the $\ell^2$ norm. Then the function $x\mapsto\bigl||\xi(x)|^2-|\eta(x)|^2\bigr|$ is summable over $G$, and
--   $$\sum_{x\in G}\Bigl||\xi(x)|^2-|\eta(x)|^2\Bigr|\le\|\xi-\eta\|_2\,\bigl(\|\xi\|_2+\|\eta\|_2\bigr).$$
--
--   The map $\xi\mapsto|\xi|^2$ sends unit vectors of $\ell^2(G)$ to probability densities on $G$, and the estimate says that it is Lipschitz from $\ell^2$ to $\ell^1$ on bounded sets, with constant $2$ on the unit sphere. It is the analytic estimate behind the translation-error bound for the means $b\mapsto\sum_x|\xi(x)|^2\,b(x^{-1})$ built from almost invariant vectors.
--
--   **Formalization Note** The ambient file assumes a group structure and a topology on $G$, but they are omitted from this statement. Summability is stated explicitly because Lean's unconditional sum of a non-summable family is defined to be $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/VectorMean.lean#L95-L116

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
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem OAI.Dixmier.l2_square_difference_bound (ξ η : ScalarL2 G) :
    Summable (fun x => |‖ξ x‖^2 - ‖η x‖^2|) ∧
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := by sorry
