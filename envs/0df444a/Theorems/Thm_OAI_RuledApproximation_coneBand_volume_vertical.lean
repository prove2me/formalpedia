-- Prove2me | Theorems.Thm_OAI_RuledApproximation_coneBand_volume_vertical
-- name    : OAI.RuledApproximation.coneBand_volume_vertical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:21:06.200013+00:00
-- url     : https://prove2.me/theorems/551989b6-43a0-4ab2-be4a-0fe402ff4b8a
-- title:
--   Area of the band $\{d\le z_1\le a,\ |z_0|\le z_1\}$ by vertical slices
-- statement:
--   For real numbers $d$ and $a$ let $B_{d,a}=\{(z_0,z_1)\in\mathbb{R}^2:\ d\le z_1\le a,\ |z_0|\le z_1\}$. If $a\le2$, then
--
--   $$
--   |B_{d,a}|=\int_{-2}^{2}\max\big(a-\max(d,|b|),\,0\big)\,db ,
--   $$
--
--   where $|B_{d,a}|$ is the Lebesgue area. No condition on $d$ is required.
--
--   The formula expresses the area of the band as an integral over the horizontal coordinate $b=z_0$: above the abscissa $b$ the band occupies the vertical segment from $\max(d,|b|)$ to $a$. In the singular covering construction the base domain of the ruled families has the same vertical-slice description with the top $a=\tfrac12$ replaced by a raised ceiling depending on $b$, so writing both areas as integrals over the common interval $[-2,2]$ allows the difference of the two areas to be computed slice by slice.
--
--   **Formalization Note** The left side is `volume.real (coneBand d a)`, and the right side is the set integral over `Icc (-2) 2` with respect to Lebesgue measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/ConeVolume.lean#L86-L99

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

theorem OAI.RuledApproximation.coneBand_volume_vertical {d a : ℝ} (ha : a ≤ 2) :
    volume.real (coneBand d a) = ∫ b in Icc (-2:ℝ) 2, max (a-max d |b|) 0 := by sorry
