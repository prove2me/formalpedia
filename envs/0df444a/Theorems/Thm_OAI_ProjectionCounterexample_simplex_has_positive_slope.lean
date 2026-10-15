-- Prove2me | Theorems.Thm_OAI_ProjectionCounterexample_simplex_has_positive_slope
-- name    : OAI.ProjectionCounterexample.simplex_has_positive_slope
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:43:16.444174+00:00
-- url     : https://prove2.me/theorems/0896a249-30a8-45b1-9288-67f2610a1379
-- title:
--   Every nonzero direction sees a facet of the standard simplex
-- statement:
--   For $d\in\mathbb{N}$ let $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}\subseteq\mathbb{R}^d$ be the standard simplex. Index its $d+1$ defining inequalities by $k\in\{\Sigma,1,\dots,d\}$, with linear functionals and levels
--   $$
--   \varphi_\Sigma(x)=\sum_{i=1}^d x_i,\quad \beta_\Sigma=1,\qquad\qquad \varphi_i(x)=-x_i,\quad \beta_i=0\quad(1\le i\le d).
--   $$
--   Thus $\varphi_\Sigma$ is the outward functional of the slanted facet opposite the origin and $\varphi_i$ that of the coordinate facet $x_i=0$.
--
--   For every nonzero vector $u\in\mathbb{R}^d$ there is an index $k\in\{\Sigma,1,\dots,d\}$ with $\varphi_k(u)>0$; explicitly,
--   $$
--   \sum_{i=1}^d u_i>0\qquad\text{or}\qquad u_i<0\ \text{ for some } i .
--   $$
--
--   Equivalently, no nonzero direction satisfies $\varphi_k(u)\le 0$ for all $k$, i.e. the recession cone of the simplex is trivial. In the language of visible faces, every nonzero direction $u$ has at least one facet of $T_d$ visible from it, which is the hypothesis needed to apply the visible-facet projection formula to the simplex in every direction.
--
--   **Formalization Note** Facets are indexed by `Option (Fin d)` (`none` for the slanted facet), and the functionals are `simplexFunctional d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean#L54-L71

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

theorem OAI.ProjectionCounterexample.simplex_has_positive_slope {d : ℕ} {u : E d} (hu : u ≠ 0) :
    ∃ i, 0 < simplexFunctional d i u := by sorry
