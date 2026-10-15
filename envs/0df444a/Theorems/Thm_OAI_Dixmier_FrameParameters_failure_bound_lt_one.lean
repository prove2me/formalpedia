-- Prove2me | Theorems.Thm_OAI_Dixmier_FrameParameters_failure_bound_lt_one
-- name    : OAI.Dixmier.FrameParameters.failure_bound_lt_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:15.799971+00:00
-- url     : https://prove2.me/theorems/8debe982-287b-470e-bdfc-77b4c03b0fdb
-- title:
--   The union-bound failure estimate $2n^p9^{k+p}e^{-25k/2}<1$
-- statement:
--   Let $n,k,p$ be natural numbers with $n\ge2$, $k\ge1$, $p\le k$ and $p\log n\le k$, where $\log$ is the natural logarithm. Then
--
--   $$2\,n^{p}\,9^{k+p}\,e^{-25k/2}<1 .$$
--
--   The left-hand side is the union bound in the random construction of frames: $n^p\cdot9^p\cdot9^k$ bounds the number of bilinear tests (an injective choice of $p$ of the $n$ vectors together with points of quarter-nets of the unit spheres of $\mathbb{R}^p$ and $\mathbb{R}^k$), and $2e^{-25k/2}$ bounds the proportion of sign matrices failing a single test. The inequality therefore guarantees that some sign matrix passes all tests.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FrameParameters.lean#L39-L68

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

open OAI OAI.Dixmier OAI.Dixmier.FrameParameters

theorem OAI.Dixmier.FrameParameters.failure_bound_lt_one {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hp : p ≤ k) (hplog : (p : ℝ) * Real.log n ≤ k) :
    2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1 := by sorry
