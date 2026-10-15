-- Prove2me | Theorems.Thm_OAI_Dixmier_FrameParameters_bounds
-- name    : OAI.Dixmier.FrameParameters.bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:57.186237+00:00
-- url     : https://prove2.me/theorems/68f6c192-0f4c-484b-8411-dc06f504087c
-- title:
--   Arithmetic bounds for the frame dimension $\lceil 2r\log(2n)\rceil$ and subfamily size $\min(2r,n)$
-- statement:
--   For integers $n\ge2$ and $r\ge1$ put
--
--   $$k=\big\lceil 2r\log(2n)\big\rceil,\qquad p=\min(2r,n),$$
--
--   where $\log$ is the natural logarithm. Then:
--
--   1. $k\ge1$;
--   2. $p\le k$;
--   3. $p\log n\le k$.
--
--   Here $k$ is the dimension of the space in which a random sign frame of $n$ vectors is built, and $p$ is the size of the subfamilies whose synthesis operators must be bounded. The three inequalities are exactly the hypotheses under which the union-bound failure estimate $2n^p9^{k+p}e^{-25k/2}<1$ holds.
--
--   **Formalization Note** $k$ and $p$ are `FrameParameters.dimension n r` (defined with `Nat.ceil`) and `FrameParameters.subfamilySize n r`; the third inequality is stated in $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FrameParameters.lean#L14-L37

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

theorem OAI.Dixmier.FrameParameters.bounds {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    1 ≤ dimension n r ∧ subfamilySize n r ≤ dimension n r ∧
      (subfamilySize n r : ℝ) * Real.log n ≤ dimension n r := by sorry
