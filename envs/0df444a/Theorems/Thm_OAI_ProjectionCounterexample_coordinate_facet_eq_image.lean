-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_coordinate_facet_eq_image
-- name    : OAI.ProjectionCounterexample.coordinate_facet_eq_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:43:54.382322+00:00
-- url     : https://prove2.me/theorems/af08be77-01ff-4151-9ae5-f2b1a505627f
-- title:
--   Coordinate facets of the simplex are isometric copies of the lower-dimensional simplex
-- statement:
--   Let $n\in\mathbb{N}$, let $T_m=\operatorname{conv}\{0,e_1,\dots,e_m\}\subseteq\mathbb{R}^m$ denote the standard simplex, and fix a coordinate position $i\in\{1,\dots,n+1\}$. Let $\iota_i:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the map that inserts a zero in position $i$,
--   $$
--   \iota_i(y_1,\dots,y_n)=(y_1,\dots,y_{i-1},\,0,\,y_i,\dots,y_n),
--   $$
--   a linear isometry of Euclidean spaces. Then the facet of $T_{n+1}$ on the coordinate hyperplane $x_i=0$ is the image of $T_n$:
--   $$
--   \{x\in T_{n+1}:\ x_i=0\}=\iota_i(T_n).
--   $$
--
--   Since $\iota_i$ is an isometry, this identifies each coordinate facet of $T_{n+1}$ with $T_n$ metrically, so its $n$-dimensional measure and the shadows of it can be computed in the parameter space $\mathbb{R}^n$. It is one of the explicit facet charts behind the projection-volume formula for simplices and for the product $T_{10}\times T_{10}$.
--
--   **Formalization Note** Coordinates are indexed by `Fin (n + 1)` (starting at $0$), and $\iota_i$ is the linear isometry `insertZero i`, built from `Fin.insertNth`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCoordinates.lean#L37-L59

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
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates

open OAI OAI.ProjectionCounterexample
open Set

theorem OAI.ProjectionCounterexample.coordinate_facet_eq_image {n : ℕ} (i : Fin (n + 1)) :
    {x ∈ simplex (n + 1) | x i = 0} = insertZero i '' simplex n := by sorry
