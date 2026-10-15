-- Prove2me | Theorems.Thm_OAI_RuledApproximation_IsTriangle_linear_image
-- name    : OAI.RuledApproximation.IsTriangle.linear_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:23:25.308814+00:00
-- url     : https://prove2.me/theorems/fed5e4b2-f769-4960-bf76-97b8250546eb
-- title:
--   Injective linear images of non-degenerate triangles are triangles
-- statement:
--   Let $E$ and $F$ be real vector spaces (of arbitrary dimension; no norm or topology is involved). A subset $P\subseteq E$ is called a **triangle** if there are a point $c\in E$ and two linearly independent vectors $u,v\in E$ such that
--
--   $$
--   P=\{\,c+s\,u+t\,v \;:\; s\ge 0,\ t\ge 0,\ s+t\le 1\,\},
--   $$
--
--   that is, $P$ is the solid, non-degenerate triangle with vertices $c$, $c+u$ and $c+v$.
--
--   **Theorem.** If $P\subseteq E$ is a triangle and $f\colon E\to F$ is an injective linear map, then the image $f(P)$ is a triangle in $F$. Explicitly, if $P$ is given by $c,u,v$ as above, then
--
--   $$
--   f(P)=\{\,f(c)+s\,f(u)+t\,f(v) \;:\; s\ge 0,\ t\ge 0,\ s+t\le 1\,\},
--   $$
--
--   and $f(u)$, $f(v)$ are again linearly independent.
--
--   In the cylinder-covering problems of this development, the base of a cylinder is a planar set lying in the plane orthogonal to the cylinder's axis, and a "triangle cylinder" is one whose base is a triangle in this sense. The lemma lets triangular bases be moved along injective linear maps, for example from a reference triangle in $\mathbb{R}^2$ into the orthogonal plane of an axis, or by a rotation of space, without losing the triangle shape; it is used to certify the two triangular tip cylinders in the singular tetrahedron cover.
--
--   **Formalization Note** The predicate is `IsTriangle`, and linear independence of the pair is stated as `LinearIndependent ℝ ![u, v]`. Only injectivity of the `ℝ`-linear map `f` is assumed; surjectivity is not needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/TipCylinders.lean#L12-L26

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Definitions.Def_OAI_Geometry_RuledCovering_EnergyIntegral
import Definitions.Def_OAI_Geometry_RuledCovering_TipCylinders

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.IsTriangle.linear_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {P : Set E} (hP : IsTriangle P) (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    IsTriangle (f '' P) := by sorry
