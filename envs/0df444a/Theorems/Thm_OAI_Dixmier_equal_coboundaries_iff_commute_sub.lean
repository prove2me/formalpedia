-- Prove2me | Theorems.Thm_OAI_Dixmier_equal_coboundaries_iff_commute_sub
-- name    : OAI.Dixmier.equal_coboundaries_iff_commute_sub
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:40.051078+00:00
-- url     : https://prove2.me/theorems/50088014-5e00-434f-9220-b9b01e108578
-- title:
--   Two elements have the same coboundary at $g$ iff their difference commutes with $U(g)$
-- statement:
--   Let $G$ be a group, $R$ a ring, and $U\colon G\to R$ a monoid homomorphism into the multiplicative monoid of $R$; thus $U(g)$ is invertible with inverse $U(g^{-1})$. For $T\in R$ define the coboundary
--
--   $$\delta_T(g)=T-U(g)\,T\,U(g^{-1})\qquad(g\in G).$$
--
--   Then for all $T,B\in R$ and every $g\in G$,
--
--   $$\delta_T(g)=\delta_B(g)\iff U(g)\,(T-B)=(T-B)\,U(g).$$
--
--   Consequently two elements implement the same coboundary at every $g\in G$ exactly when their difference lies in the commutant of $U(G)$. For bounded operators on a Hilbert space this is how two implementers of the same cocycle are compared: they differ by an operator commuting with the representation.
--
--   **Formalization Note** The coboundary is `coboundary U T g`, defined as `T - conjugate U g T` with `conjugate U g T` equal to $U(g)\,T\,U(g^{-1})$; commutation is Mathlib's `Commute`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Cocycle.lean#L49-L64

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

open OAI OAI.Dixmier
variable {G R : Type*} [Group G] [Ring R]

theorem OAI.Dixmier.equal_coboundaries_iff_commute_sub (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by sorry
