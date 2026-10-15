-- Prove2me | Theorems.Thm_OAI_RuledApproximation_Cylinder_translate_carrier
-- name    : OAI.RuledApproximation.Cylinder.translate_carrier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:52:13.981893+00:00
-- url     : https://prove2.me/theorems/59e14753-4924-4c61-8f8c-0c952df78ef8
-- title:
--   Translating a cylinder translates its carrier
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ consists of a unit vector $u$ (the axis) and a base $B$ contained in the plane $u^\perp$; its carrier is $\mathrm{carrier}(C)=\{b+tu:\ b\in B,\ t\in\mathbb{R}\}$. For $q\in\mathbb{R}^3$ let $q^\perp=q-\langle u,q\rangle u\in u^\perp$ be the component of $q$ orthogonal to the axis, and let $C+q$ denote the translated cylinder, with the same axis $u$ and base $q^\perp+B=\{q^\perp+b:\ b\in B\}$. Then
--   $$
--   \mathrm{carrier}(C+q)=q+\mathrm{carrier}(C)=\{q+x:\ x\in\mathrm{carrier}(C)\}.
--   $$
--
--   The translated cylinder is again a cylinder in the sense of the covering problem, its base being a translate of $B$ inside the same plane $u^\perp$. The identity is the translation step in transporting finite cylinder covers along isometries of $\mathbb{R}^3$, which is needed for the isometry-invariant form of the covering statements.
--
--   **Formalization Note** The translated cylinder is `C.translate q`, whose base is the image of `C.base` under `b ↦ C.transversePart q + b` inside the subtype `(span ℝ {C.axis})ᗮ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Isometries.lean#L77-L91

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

theorem OAI.RuledApproximation.Cylinder.translate_carrier (C : Cylinder) (q : Space) :
    (C.translate q).carrier = (fun x => q + x) '' C.carrier := by sorry
