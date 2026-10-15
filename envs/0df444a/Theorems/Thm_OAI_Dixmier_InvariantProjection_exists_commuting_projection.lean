-- Prove2me | Theorems.Thm_OAI_Dixmier_InvariantProjection_exists_commuting_projection
-- name    : OAI.Dixmier.InvariantProjection.exists_commuting_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:31:21.513641+00:00
-- url     : https://prove2.me/theorems/218ef010-ea63-4493-be08-676d753848ef
-- title:
--   Unitarizable representations admit commuting bounded projections onto closed invariant subspaces
-- statement:
--   Let $H$ be a complex Hilbert space, $G$ a group, and $\pi\colon G\to B(H)$ a homomorphism into the monoid of bounded linear operators on $H$, so that each $\pi(g)$ is invertible with inverse $\pi(g^{-1})$. Suppose $\pi$ is similar to a unitary representation: there is a bounded invertible operator $S$ on $H$ with bounded inverse such that
--
--   $$\|S\,\pi(g)\,S^{-1}x\|=\|x\|\qquad\text{for all }g\in G,\ x\in H .$$
--
--   Let $M\subseteq H$ be a closed subspace that is invariant under $\pi$, i.e. $\pi(g)x\in M$ whenever $x\in M$. Then there is a bounded operator $P$ on $H$ such that
--
--   1. $Px\in M$ for every $x\in H$;
--   2. $Px=x$ for every $x\in M$;
--   3. $P\,\pi(g)=\pi(g)\,P$ for every $g\in G$.
--
--   Thus $P$ is a bounded idempotent with range $M$ that commutes with the representation, so $M$ has the $\pi$-invariant complement $\ker P$. This complementation property of unitarizable representations is the mechanism by which a unitarizing similarity forces cocycles to be inner.
--
--   **Formalization Note** Similarity to a unitary representation is `SimilarToUnitary π`: there is a continuous linear equivalence $S$ of $H$ such that every $S\pi(g)S^{-1}$ is norm-preserving; no bound on $\|S\|$ or $\|S^{-1}\|$ is imposed. $M$ is a `ClosedSubmodule ℂ H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/InvariantProjection.lean#L45-L77

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

open OAI OAI.Dixmier OAI.Dixmier.InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.Dixmier.InvariantProjection.exists_commuting_projection (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by sorry
