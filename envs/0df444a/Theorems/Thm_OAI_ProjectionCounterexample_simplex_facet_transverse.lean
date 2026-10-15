-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_simplex_facet_transverse
-- name    : OAI.ProjectionCounterexample.simplex_facet_transverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:58.197069+00:00
-- url     : https://prove2.me/theorems/dc1e0d5d-7222-49d7-a40c-98f8a2e82eec
-- title:
--   Distinct facet hyperplanes of the simplex cut each facet chart transversally
-- statement:
--   Let $n\ge 1$ and consider the standard simplex $T_{n+1}=\operatorname{conv}\{0,e_1,\dots,e_{n+1}\}\subseteq\mathbb{R}^{n+1}$. Its facets are indexed by $k\in\{\Sigma,1,\dots,n+1\}$, with outward functionals $\varphi_\Sigma(x)=\sum_{j=1}^{n+1}x_j$ for the slanted facet and $\varphi_i(x)=-x_i$ for the coordinate facet $x_i=0$. Each facet carries an affine chart $z\mapsto c_k+L_k z$ from $\mathbb{R}^n$, with linear parts $L_k:\mathbb{R}^n\to\mathbb{R}^{n+1}$ given by
--   $$
--   L_\Sigma(z)=\Bigl(z_1,\dots,z_n,\ -\sum_{j=1}^n z_j\Bigr),\qquad L_i(z)=\iota_i(z)\quad(1\le i\le n+1),
--   $$
--   where $\iota_i$ inserts a zero in position $i$ (the centers are $c_\Sigma=e_{n+1}$ and $c_i=0$). Then for any two distinct indices $k\ne l$,
--   $$
--   \varphi_l\circ L_k\ne 0
--   $$
--   as a linear functional on $\mathbb{R}^n$.
--
--   Geometrically, the defining functional of any other facet is not constant on the affine hull of facet $k$, so the hyperplane of facet $l$ meets that affine hull in a proper affine subspace. This transversality is the hypothesis under which the intersection of two distinct facets, and its image under a linear projection, is shown to be negligible for $n$-dimensional Hausdorff measure, as needed when the projection volume of the simplex is written as a sum over its facets. The assumption $n\ge 1$ is necessary: for $n=0$ the parameter space $\mathbb{R}^0$ is a point and every linear functional on it vanishes.
--
--   **Formalization Note** Facets are indexed by `Option (Fin (n + 1))`, with `none` the slanted facet; $L_k$ is `simplexFacetLinear n k` (for `none` the graph map `graphLinear (Fin.last n) (allOnes n)`, for `some i` the isometry `insertZero i`), and $\varphi_l$ is `simplexFunctional (n + 1) l`. Coordinates are indexed from $0$ in Lean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexFacetCharts.lean#L47-L75

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
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts

open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem OAI.ProjectionCounterexample.simplex_facet_transverse {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) :
    (simplexFunctional (n + 1) j).comp (simplexFacetLinear n i) ≠ 0 := by sorry
