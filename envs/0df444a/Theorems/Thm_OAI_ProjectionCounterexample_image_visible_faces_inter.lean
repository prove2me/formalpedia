-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_image_visible_faces_inter
-- name    : OAI.ProjectionCounterexample.image_visible_faces_inter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:39.009036+00:00
-- url     : https://prove2.me/theorems/1560a8ef-a4fc-4c3c-a1bf-e5fa17ac77da
-- title:
--   Shadows of two visible faces overlap exactly in the shadow of their intersection
-- statement:
--   Let $V$ and $W$ be real vector spaces, let $I$ be an arbitrary index set, let $(a_i)_{i\in I}$ be a family of linear functionals $a_i:V\to\mathbb{R}$ and $(b_i)_{i\in I}$ a family of real numbers. Write
--   $$
--   K=\{x\in V:\ a_i(x)\le b_i\ \text{ for all } i\in I\}
--   $$
--   for the corresponding intersection of closed halfspaces, and $F_i=\{x\in K:\ a_i(x)=b_i\}$ for the part of $K$ on the $i$-th bounding hyperplane. For a direction $u\in V$ we call $F_i$ *visible from $u$* when $a_i(u)>0$, i.e. when $u$ points out of $K$ through the $i$-th constraint.
--
--   Let $u\in V$ and let $q:V\to W$ be a linear map whose kernel is exactly the line spanned by $u$, $\ker q=\mathbb{R}u$. If $i,j\in I$ satisfy $a_i(u)>0$ and $a_j(u)>0$, then
--   $$
--   q(F_i)\cap q(F_j)=q(F_i\cap F_j).
--   $$
--
--   Typically $q$ is the orthogonal projection onto the hyperplane $u^\perp$, and the statement says that the shadows of two faces visible from $u$ overlap only along the shadow of their intersection $F_i\cap F_j$; for two distinct facets of a polytope this intersection is a face of lower dimension. This is what makes the projection volume of a polytope additive over its visible facets, once the shadows of facet intersections are known to be null sets. (The hypotheses force $u\ne 0$, since $a_i(0)=0$.)
--
--   **Formalization Note** $K$ is `halfspaceBody a b`, $F_i$ is `boundingFace a b i`, and the kernel condition is `LinearMap.ker q = Submodule.span ℝ {u}`; images are set images `q '' _`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCover.lean#L95-L113

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

omit [Fintype ι] in
theorem OAI.ProjectionCounterexample.image_visible_faces_inter
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hker : LinearMap.ker q = Submodule.span ℝ {u})
    {i j : ι} (hi : 0 < a i u) (hj : 0 < a j u) :
    (q '' boundingFace a b i) ∩ (q '' boundingFace a b j) =
      q '' (boundingFace a b i ∩ boundingFace a b j) := by sorry
