-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_visible_face_line_unique
-- name    : OAI.ProjectionCounterexample.visible_face_line_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:23.017845+00:00
-- url     : https://prove2.me/theorems/549a7b8b-bdd0-43bf-8b8c-5082f165d06d
-- title:
--   Visible faces meet each line in the viewing direction at most once
-- statement:
--   Let $V$ be a real vector space, let $I$ be an arbitrary index set, let $(a_i)_{i\in I}$ be a family of linear functionals $a_i:V\to\mathbb{R}$ and $(b_i)_{i\in I}$ a family of real numbers. Write
--   $$
--   K=\{x\in V:\ a_i(x)\le b_i\ \text{ for all } i\in I\}
--   $$
--   for the corresponding intersection of closed halfspaces, and $F_i=\{x\in K:\ a_i(x)=b_i\}$ for the part of $K$ on the $i$-th bounding hyperplane. For a direction $u\in V$ we call $F_i$ *visible from $u$* when $a_i(u)>0$, i.e. when $u$ points out of $K$ through the $i$-th constraint.
--
--   Let $u\in V$, and let $i,j\in I$ be indices (equal or not) with $a_i(u)>0$ and $a_j(u)>0$. If $y\in F_i$, $z\in F_j$ and $z=y+t\,u$ for some $t\in\mathbb{R}$, then
--   $$
--   z=y .
--   $$
--
--   Equivalently, the union of all faces visible from $u$ meets every line parallel to $u$ in at most one point, so any linear map whose kernel is the line $\mathbb{R}u$ is injective on that union. This is the reason why the shadows of two visible faces overlap only in the shadow of their common part.
--
--   **Formalization Note** $K$ is `halfspaceBody a b` and $F_i$ is `boundingFace a b i`; no finiteness of the index type is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCover.lean#L75-L93

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
theorem OAI.ProjectionCounterexample.visible_face_line_unique
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {i j : ι} {y z u : V} {t : ℝ}
    (hy : y ∈ boundingFace a b i) (hz : z ∈ boundingFace a b j)
    (hi : 0 < a i u) (hj : 0 < a j u) (hline : z = y + t • u) : z = y := by sorry
