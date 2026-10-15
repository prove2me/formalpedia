-- Prove2me | Theorems.Thm_OAI_Dixmier_FiniteSigns_upper_tail_mgf
-- name    : OAI.Dixmier.FiniteSigns.upper_tail_mgf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:38.949768+00:00
-- url     : https://prove2.me/theorems/0f60a2cc-d20f-4dc8-b0b4-5167680cc131
-- title:
--   Exponential moment bound for the upper tail of a weighted sum of random signs
-- statement:
--   Let $J$ be a finite set and $a=(a_j)_{j\in J}$ a family of real coefficients. For a sign vector $\epsilon=(\epsilon_j)_{j\in J}\in\{-1,1\}^J$ write
--   $$S_a(\epsilon)=\sum_{j\in J}a_j\,\epsilon_j,$$
--   and for a condition $P$ on sign vectors let $\#\{\epsilon:P(\epsilon)\}$ be the number of the $2^{|J|}$ sign vectors satisfying it. Then for all real numbers $t\ge0$ and $u$,
--   $$\#\bigl\{\epsilon:\ S_a(\epsilon)>u\bigr\}\cdot e^{tu}\le2^{|J|}\exp\Bigl(\frac{t^2}{2}\sum_{j\in J}a_j^2\Bigr).$$
--
--   Dividing by $2^{|J|}$, this says that for independent uniformly random signs $\epsilon_j$ one has $\Pr[S_a>u]\le\exp\bigl(-tu+\tfrac{t^2}{2}\sum_ja_j^2\bigr)$ for every $t\ge0$; choosing $t$ suitably gives sub-Gaussian tail bounds. Probabilities are expressed as counts over the finite cube of sign vectors, so no measure theory is involved.
--
--   **Formalization Note** Sign vectors are Boolean functions $\sigma:J\to\{\mathrm{true},\mathrm{false}\}$, with `sign true = 1` and `sign false = -1`, so that $S_a$ is `value a σ`; the count is the cardinality of a finite set of such functions, cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSigns.lean#L47-L62

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

theorem OAI.Dixmier.FiniteSigns.upper_tail_mgf (a : J → ℝ) {t u : ℝ} (ht : 0 ≤ t) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) * Real.exp (t*u) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (t^2 * (∑ j, (a j)^2) / 2) := by sorry
