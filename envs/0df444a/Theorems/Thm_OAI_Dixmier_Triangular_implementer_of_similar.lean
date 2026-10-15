-- Prove2me | Theorems.Thm_OAI_Dixmier_Triangular_implementer_of_similar
-- name    : OAI.Dixmier.Triangular.implementer_of_similar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:31:41.292365+00:00
-- url     : https://prove2.me/theorems/7cbb9a6e-6daa-49b7-8b55-e321da732ae5
-- title:
--   A unitarizing similarity of a triangular representation makes its cocycle inner
-- statement:
--   Let $H$ be a complex Hilbert space, $G$ a group, $U\colon G\to B(H)$ a homomorphism into the monoid of bounded operators on $H$, and $D\colon G\to B(H)$ a cocycle for conjugation by $U$:
--
--   $$D(1)=0,\qquad D(gh)=D(g)+U(g)\,D(h)\,U(g^{-1})\qquad(g,h\in G).$$
--
--   On $H\oplus H$, normed by $\|(x_1,x_2)\|^2=\|x_1\|^2+\|x_2\|^2$, consider the upper triangular representation
--
--   $$\pi(g)=\begin{pmatrix}U(g)&D(g)\,U(g)\\0&U(g)\end{pmatrix},\qquad\pi(g)(x_1,x_2)=\big(U(g)x_1+D(g)U(g)x_2,\ U(g)x_2\big).$$
--
--   If $\pi$ is similar to a unitary representation, i.e. there is a bounded invertible operator $S$ on $H\oplus H$ with bounded inverse such that every $S\pi(g)S^{-1}$ is norm-preserving, then $D$ is inner: there is a bounded operator $B$ on $H$ with
--
--   $$D(g)=B-U(g)\,B\,U(g^{-1})\qquad\text{for all }g\in G .$$
--
--   Contrapositively, to show that a uniformly bounded representation of this triangular form is not similar to a unitary one, it suffices to show that its cocycle $D$ is not the coboundary of any bounded operator. This is the obstruction used to build uniformly bounded non-unitarizable representations of nonamenable groups.
--
--   **Formalization Note** No unitarity of $U$ and no bound on $D$ are assumed. $H\oplus H$ is `Triangular.Double H`, i.e. `WithLp 2 (H × H)`, $\pi$ is `Triangular.representation U D h1 hD`, and similarity is `SimilarToUnitary`. The conclusion is `D g = coboundary U B g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Unitarizer.lean#L15-L53

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

open OAI OAI.Dixmier OAI.Dixmier.Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.Dixmier.Triangular.implementer_of_similar (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by sorry
