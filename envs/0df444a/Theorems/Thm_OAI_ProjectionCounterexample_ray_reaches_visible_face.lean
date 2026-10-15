-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_ray_reaches_visible_face
-- name    : OAI.ProjectionCounterexample.ray_reaches_visible_face
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:41:16.061955+00:00
-- url     : https://prove2.me/theorems/8bfc7c8d-ffa2-4a0f-a9ec-ca226f26f214
-- title:
--   A ray from a point of a polyhedron reaches a face visible from its direction
-- statement:
--   Let $V$ be a real vector space, let $I$ be a finite index set, let $(a_i)_{i\in I}$ be a family of linear functionals $a_i:V\to\mathbb{R}$ and $(b_i)_{i\in I}$ a family of real numbers. Write
--   $$
--   K=\{x\in V:\ a_i(x)\le b_i\ \text{ for all } i\in I\}
--   $$
--   for the corresponding intersection of closed halfspaces, and $F_i=\{x\in K:\ a_i(x)=b_i\}$ for the part of $K$ on the $i$-th bounding hyperplane. For a direction $u\in V$ we call $F_i$ *visible from $u$* when $a_i(u)>0$, i.e. when $u$ points out of $K$ through the $i$-th constraint.
--
--   Let $y\in K$ and let $u\in V$ satisfy $a_i(u)>0$ for at least one index $i$. Then there are a parameter $t\ge 0$ and an index $i\in I$ with $a_i(u)>0$ such that
--   $$
--   y+t\,u\in F_i .
--   $$
--
--   In words, starting from any point of $K$ and moving in a direction $u$ from which at least one face is visible, one reaches a face visible from $u$ after a nonnegative time. Applied to the direction of an orthogonal projection, it shows that the shadow of $K$ along $u$ is covered by the shadows of the faces visible from $u$; this is the covering half of the formula that expresses the projection volume of a polytope as a sum over its visible facets. No boundedness of $K$ and no finite dimensionality of $V$ are needed.
--
--   **Formalization Note** $K$ is `halfspaceBody a b` and $F_i$ is `boundingFace a b i`; the index type carries a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCover.lean#L28-L56

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover

open OAI OAI.ProjectionCounterexample
open Set
variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem OAI.ProjectionCounterexample.ray_reaches_visible_face (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {y u : V} (hy : y ∈ halfspaceBody a b) (hu : ∃ i, 0 < a i u) :
    ∃ (t : ℝ) (i : ι), 0 ≤ t ∧ 0 < a i u ∧
      y + t • u ∈ boundingFace a b i := by sorry
