-- Prove2me | Theorems.Thm_OAI_RuledApproximation_coneBand_volume
-- name    : OAI.RuledApproximation.coneBand_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:19:56.6272+00:00
-- url     : https://prove2.me/theorems/e31ca90c-35c4-48d2-8f82-dca4b0d96f2f
-- title:
--   The truncated triangle $\{d\le z_1\le a,\ |z_0|\le z_1\}$ has area $a^2-d^2$
-- statement:
--   For real numbers $d$ and $a$ let
--
--   $$
--   B_{d,a}=\{(z_0,z_1)\in\mathbb{R}^2:\ d\le z_1\le a,\ |z_0|\le z_1\}.
--   $$
--
--   If $0\le d\le a$, then the Lebesgue area of $B_{d,a}$ is
--
--   $$
--   |B_{d,a}|=a^2-d^2 .
--   $$
--
--   For $0\le d\le a$ the set $B_{d,a}$ is the trapezoid obtained from the triangle $\{0\le z_1\le a,\ |z_0|\le z_1\}$, of area $a^2$, by removing the part below height $d$. In the singular covering construction it is the reference shape for the base domain of the ruled families, which removes the tip below height $d=c^\gamma$ from the triangle of height $a=\tfrac12$; the formula gives this reference area $\tfrac14-(c^\gamma)^2$.
--
--   **Formalization Note** The area is `volume.real (coneBand d a)`, the real-valued Lebesgue measure on `Plane`. The hypothesis $d\ge0$ matters: for $d<0\le a$ the set is the full triangle, of area $a^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/ConeVolume.lean#L63-L84

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

theorem OAI.RuledApproximation.coneBand_volume {d a : ℝ} (hd : 0 ≤ d) (hda : d ≤ a) :
    volume.real (coneBand d a) = a^2-d^2 := by sorry
