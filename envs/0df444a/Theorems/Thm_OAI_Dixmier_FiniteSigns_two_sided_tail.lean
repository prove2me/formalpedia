-- Prove2me | Theorems.Thm_OAI_Dixmier_FiniteSigns_two_sided_tail
-- name    : OAI.Dixmier.FiniteSigns.two_sided_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:14.62889+00:00
-- url     : https://prove2.me/theorems/9e5d0eab-7fae-4382-a61e-c8c9f4a8848f
-- title:
--   Two-sided sub-Gaussian tail for weighted sums of random signs with $\sum_j a_j^2=1/k$
-- statement:
--   Let $J$ be a finite set and $a=(a_j)_{j\in J}$ a family of real coefficients. For a sign vector $\epsilon=(\epsilon_j)_{j\in J}\in\{-1,1\}^J$ write
--   $$S_a(\epsilon)=\sum_{j\in J}a_j\,\epsilon_j,$$
--   and for a condition $P$ on sign vectors let $\#\{\epsilon:P(\epsilon)\}$ be the number of the $2^{|J|}$ sign vectors satisfying it. Let $k>0$ and $u>0$ be real numbers and assume $\sum_{j\in J}a_j^2=1/k$. Then
--   $$\frac{\#\bigl\{\epsilon:\ |S_a(\epsilon)|>u\bigr\}}{2^{|J|}}\le2\,e^{-ku^2/2}.$$
--
--   In probabilistic language: if the $\epsilon_j$ are independent uniformly random signs and $\sum_ja_j^2=1/k$, then $\Pr\bigl[|S_a|>u\bigr]\le2e^{-ku^2/2}$, a sub-Gaussian tail with variance $1/k$. Such tail bounds are combined with nets on spheres to show that random sign matrices have small operator norm with positive probability.
--
--   **Formalization Note** Sign vectors are Boolean functions $\sigma:J\to\{\mathrm{true},\mathrm{false}\}$, with `sign true = 1` and `sign false = -1`, so that $S_a$ is `value a σ`; the count is the cardinality of a finite set of such functions, cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSigns.lean#L79-L102

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

open OAI OAI.Dixmier OAI.Dixmier.FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
attribute [local instance] OAI.Dixmier.FiniteSigns.instDecidableEq_oAI

theorem OAI.Dixmier.FiniteSigns.two_sided_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card J ≤ 2 * Real.exp (-k*u^2/2) := by sorry
