-- Prove2me | Theorems.Thm_OAI_Dixmier_HilbertSum_separableSpace
-- name    : OAI.Dixmier.HilbertSum.separableSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:57.321437+00:00
-- url     : https://prove2.me/theorems/04978357-506b-4e24-84e6-d59f0d92988e
-- title:
--   A countable Hilbert direct sum of separable inner product spaces is separable
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of complex inner product spaces indexed by a countable set $I$, and suppose that every $E_i$ is separable. Then the $\ell^2$ direct sum
--
--   $$\bigoplus_{i\in I}^{\ell^2}E_i=\Big\{x\in\prod_{i\in I}E_i:\ \sum_{i\in I}\|x_i\|^2<\infty\Big\},\qquad\|x\|=\Big(\sum_{i\in I}\|x_i\|^2\Big)^{1/2},$$
--
--   is a separable space.
--
--   In the construction of uniformly bounded non-unitarizable representations, the representation space is an $\ell^2$ sum over countably many stages, each of which is an $\ell^2$ sum of finite-dimensional fibres over the countable group; this result shows that such spaces are separable, as the definition of a witness requires.
--
--   **Formalization Note** The direct sum is Mathlib's `lp E 2` (here `HilbertSum.Space E`). The spaces $E_i$ are not required to be complete. Separability is `TopologicalSpace.SeparableSpace`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/HilbertSum.lean#L132-L151

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
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum

open OAI OAI.Dixmier OAI.Dixmier.HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
attribute [local instance] OAI.Dixmier.HilbertSum.instDecidableEq_oAI

theorem OAI.Dixmier.HilbertSum.separableSpace [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by sorry
