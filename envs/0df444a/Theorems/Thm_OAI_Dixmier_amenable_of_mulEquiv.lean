-- Prove2me | Theorems.Thm_OAI_Dixmier_amenable_of_mulEquiv
-- name    : OAI.Dixmier.amenable_of_mulEquiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:33:48.732005+00:00
-- url     : https://prove2.me/theorems/9cb7c244-1318-4cf5-b8a6-42506b01ffbf
-- title:
--   Amenability of discrete groups is invariant under group isomorphisms
-- statement:
--   Let $G$ and $Q$ be groups, each carrying the discrete topology, and let $e:G\to Q$ be a group isomorphism. A discrete group $\Gamma$ is called *amenable* here if there is a $\mathbb C$-linear functional $m$ on the space $\ell^\infty(\Gamma)$ of bounded functions $\Gamma\to\mathbb C$ that is normalized, $m(\mathbf 1)=1$; positive, in the sense that $m(f)$ is a nonnegative real number whenever every value $f(x)$ is a nonnegative real number; and left-invariant, $m(\lambda_gf)=m(f)$ for all $g\in\Gamma$ and $f\in\ell^\infty(\Gamma)$, where $(\lambda_gf)(x)=f(g^{-1}x)$. The theorem states:
--
--   $$
--   Q\ \text{is amenable}\quad\Longrightarrow\quad G\ \text{is amenable}.
--   $$
--
--   In other words, this notion of amenability is invariant under group isomorphisms. Its use is to transfer amenability, and hence nonamenability, between a group and an isomorphic copy of it, for instance a copy realized in a different type universe.
--
--   **Formalization Note** $G$ and $Q$ may live in different type universes. The space $\ell^\infty$ is modelled by bounded continuous functions `G →ᵇ ℂ`, which for the discrete topology are exactly the bounded functions, and the mean is only required to be linear, not continuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/UniverseTransport.lean#L27-L40

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
import Definitions.Def_OAI_Analysis_Unitarizability_Masked
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport

open OAI OAI.Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

theorem OAI.Dixmier.amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by sorry
