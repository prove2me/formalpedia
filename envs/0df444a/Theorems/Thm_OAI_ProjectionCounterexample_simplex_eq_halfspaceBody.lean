-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_halfspaceBody
-- name    : OAI.ProjectionCounterexample.simplex_eq_halfspaceBody
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:53.685291+00:00
-- url     : https://prove2.me/theorems/ee5cc799-e919-4535-adc8-67945fc6d197
-- title:
--   The standard simplex as an intersection of $d+1$ halfspaces
-- statement:
--   For $d\in\mathbb{N}$ let $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}\subseteq\mathbb{R}^d$ be the standard simplex. Index its $d+1$ defining inequalities by $k\in\{\Sigma,1,\dots,d\}$, with linear functionals and levels
--   $$
--   \varphi_\Sigma(x)=\sum_{i=1}^d x_i,\quad \beta_\Sigma=1,\qquad\qquad \varphi_i(x)=-x_i,\quad \beta_i=0\quad(1\le i\le d).
--   $$
--   Thus $\varphi_\Sigma$ is the outward functional of the slanted facet opposite the origin and $\varphi_i$ that of the coordinate facet $x_i=0$. Then $T_d$ is exactly the intersection of the corresponding halfspaces:
--   $$
--   T_d=\bigl\{x\in\mathbb{R}^d:\ \varphi_k(x)\le\beta_k\ \text{ for all } k\in\{\Sigma,1,\dots,d\}\bigr\}.
--   $$
--
--   This presents the simplex in the form required by the general facts about finite intersections of halfspaces (visible faces, rays reaching faces, overlaps of face shadows), with these particular outward functionals, which are the ones used to compute the projection volumes of $T_d$.
--
--   **Formalization Note** The index set is `Option (Fin d)`, with `none` the slanted facet and `some i` the coordinate facet $x_i=0$; the functionals are `simplexFunctional d`, the levels are `simplexLevel`, and the right-hand side is `halfspaceBody (simplexFunctional d) simplexLevel`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean#L37-L52

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

open OAI OAI.ProjectionCounterexample
open Set

theorem OAI.ProjectionCounterexample.simplex_eq_halfspaceBody (d : ℕ) :
    simplex d = halfspaceBody (simplexFunctional d) simplexLevel := by sorry
