-- Prove2me | Theorems.Thm_OAI_RuledApproximation_coneTriangle_isCompact
-- name    : OAI.RuledApproximation.coneTriangle_isCompact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:18:31.606748+00:00
-- url     : https://prove2.me/theorems/b385fd7f-f2d6-4fe1-94f7-c2ab08e4b88e
-- title:
--   The triangle $\{0\le z_1\le a,\ |z_0|\le z_1\}$ is compact
-- statement:
--   For a real number $a$ let
--
--   $$
--   T_a=\{(z_0,z_1)\in\mathbb{R}^2:\ 0\le z_1\le a,\ |z_0|\le z_1\}.
--   $$
--
--   For $a\ge0$ this is the closed isosceles right triangle with vertices $(0,0)$, $(-a,a)$ and $(a,a)$; for $a<0$ it is empty.
--
--   **Theorem.** For every real number $a$, the set $T_a$ is compact.
--
--   The triangles $T_a$ recur throughout the singular covering construction for the regular tetrahedron: $T_{1/2}$ is the limiting shape of the base domain of the two ruled families as the perturbation parameter tends to $0$, $T_2$ contains every such base domain, and the triangular tip cylinders are built over the triangles $T_{2d}$. Compactness supplies the measurability and finiteness of area needed to compute areas and integrals over these sets.
--
--   **Formalization Note** The set is `coneTriangle a` in `Plane`; no sign condition on $a$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/ConeVolume.lean#L16-L27

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

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.coneTriangle_isCompact (a : ℝ) : IsCompact (coneTriangle a) := by sorry
