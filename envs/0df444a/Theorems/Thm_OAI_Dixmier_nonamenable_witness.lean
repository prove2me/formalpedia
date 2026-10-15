-- Prove2me | Theorems.Thm_OAI_Dixmier_nonamenable_witness
-- name    : OAI.Dixmier.nonamenable_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:33:13.205004+00:00
-- url     : https://prove2.me/theorems/7bffda89-947a-4bd1-97d1-4ef42dea4c27
-- title:
--   Every countable nonamenable group has a $101$-bounded representation that is not similar to a unitary one
-- statement:
--   Let $G$ be a countable group, regarded as a discrete group. Recall the notion of amenability used here: $G$ is *amenable* if there is a $\mathbb C$-linear functional $m$ on the space $\ell^\infty(G)$ of bounded functions $f:G\to\mathbb C$ such that $m(\mathbf 1)=1$; $m(f)$ is a nonnegative real number whenever every value $f(x)$ is a nonnegative real number; and $m(\lambda_gf)=m(f)$ for all $g\in G$ and $f\in\ell^\infty(G)$, where $(\lambda_gf)(x)=f(g^{-1}x)$.
--
--   **Theorem.** If $G$ is not amenable, then there exist a separable complex Hilbert space $H$ and a group homomorphism $\pi$ from $G$ into the bounded linear operators on $H$ such that
--
--   $$
--   \|\pi(g)\|\le 101\quad\text{for all }g\in G,
--   $$
--
--   and $\pi$ is not similar to a unitary representation: there is no bounded invertible operator $S$ on $H$ with bounded inverse such that $\|S\pi(g)S^{-1}x\|=\|x\|$ for all $g\in G$ and $x\in H$.
--
--   Thus every countable nonamenable group has a uniformly bounded representation that is not unitarizable, with the explicit uniform bound $101$. Together with the classical Day–Dixmier theorem (uniformly bounded representations of amenable groups are similar to unitary ones), this shows that a countable discrete group is amenable if and only if all its uniformly bounded Hilbert-space representations are similar to unitary ones; in particular every countable discrete group all of whose uniformly bounded representations are unitarizable is amenable.
--
--   **Formalization Note** The group carries a topology that is assumed discrete, so that the bounded continuous functions `G →ᵇ ℂ` used in the definition of amenability are exactly the bounded functions; the mean is only required to be linear. The conclusion `NonamenableWitness.{u,u} G` asks for a complete, separable complex inner product space in the same type universe `u` as $G$, together with a monoid homomorphism into its continuous linear operators (so each $\pi(g)$ is invertible with inverse $\pi(g^{-1})$); similarity is witnessed by a continuous linear equivalence. The version with independent universes is obtained separately by transport along group isomorphisms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Main.lean#L16-L83

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

open OAI OAI.Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]

theorem OAI.Dixmier.nonamenable_witness (hG : ¬ Amenable G) : NonamenableWitness.{u,u} G := by sorry
