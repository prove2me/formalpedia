-- Prove2me | Theorems.Thm_OAI_Dixmier_sum_pairwise_sq
-- name    : OAI.Dixmier.sum_pairwise_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:29.986244+00:00
-- url     : https://prove2.me/theorems/69728f65-254b-4854-a93e-20ab6a45c2d6
-- title:
--   Pairwise variance identity $\sum_{i,j\in S}\|v_i-v_j\|^2=2|S|\sum_{i\in S}\|v_i\|^2-2\|\sum_{i\in S}v_i\|^2$
-- statement:
--   Let $H$ be a complex inner product space, $I$ an index set, $S\subseteq I$ a finite subset, and $v:I\to H$ a family of vectors. Then
--   $$\sum_{i\in S}\sum_{j\in S}\|v_i-v_j\|^2=2\,|S|\sum_{i\in S}\|v_i\|^2-2\,\Bigl\|\sum_{i\in S}v_i\Bigr\|^2.$$
--
--   This is the unnormalized variance identity. Dividing by $2|S|^2$ (for $S$ nonempty) gives its familiar form: half the mean squared distance between two members of the family equals the mean squared norm minus the squared norm of the mean. It is used to show that if an average of unit vectors has norm close to $1$, then all the vectors are close to one another.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Average.lean#L14-L30

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

theorem OAI.Dixmier.sum_pairwise_sq (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by sorry
