-- Prove2me | Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_isometry
-- name    : OAI.RuledApproximation.HasFiniteCover.isometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:53:04.00561+00:00
-- url     : https://prove2.me/theorems/4955e431-4366-4305-9f69-022c62c51fc6
-- title:
--   Finite parallelogram-cylinder covers are preserved by isometries of $\mathbb{R}^3$
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent.
--
--   **Theorem.** Let $S\subseteq\mathbb{R}^3$, let $A\in\mathbb{R}$, and let $F:\mathbb{R}^3\to\mathbb{R}^3$ be a bijective isometry of Euclidean space. Suppose $S$ is covered by finitely many parallelogram cylinders $C_1,\dots,C_n$ with $\sum_i\operatorname{area}(C_i)\le A$. Then there are finitely many parallelogram cylinders $C'_1,\dots,C'_m$ with
--   $$
--   F(S)\subseteq\bigcup_{j=1}^{m}\operatorname{car}(C'_j),\qquad \sum_{j=1}^{m}\operatorname{area}(C'_j)\le A .
--   $$
--
--   The cylinder-covering cost is therefore an invariant of the congruence class of a set: a cover estimate proved for a ruled set in convenient coordinates holds verbatim for every rigidly moved copy. This is what allows the isometry-invariant form of the physical hyperbolic covering statement, where the ruled set is first mapped by an arbitrary isometry $F$, to be reduced to the set in standard position.
--
--   **Formalization Note** $F$ is an isometric equivalence `Space ≃ᵢ Space` of `EuclideanSpace ℝ (Fin 3)`; the statement is `HasFiniteCover Cylinder.parallelogram S A → HasFiniteCover Cylinder.parallelogram (F '' S) A`. A cylinder's base is a subset of the orthogonal complement of the span of its axis and its area is `volume.real` of the base.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Isometries.lean#L103-L119

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

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.HasFiniteCover.isometry {S : Set Space} {A : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' S) A := by sorry
