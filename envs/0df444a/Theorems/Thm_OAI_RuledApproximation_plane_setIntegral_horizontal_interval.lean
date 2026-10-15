-- Prove2me | Theorems.Thm_OAI_RuledApproximation_plane_setIntegral_horizontal_interval
-- name    : OAI.RuledApproximation.plane_setIntegral_horizontal_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:17:12.261051+00:00
-- url     : https://prove2.me/theorems/9646af04-3170-493a-b1e8-90b1866b57bf
-- title:
--   Fubini's theorem for a planar region described by horizontal slices
-- statement:
--   Let $S\subseteq\mathbb{R}^2$ be a Lebesgue measurable set and let $f:\mathbb{R}^2\to\mathbb{R}$ be integrable on $S$. Suppose there are a measurable set $s\subseteq\mathbb{R}$ and functions $l,u:\mathbb{R}\to\mathbb{R}$ such that for every point $z=(z_0,z_1)$
--
--   $$
--   z\in S\iff z_1\in s\ \text{ and }\ l(z_1)\le z_0\le u(z_1).
--   $$
--
--   Then
--
--   $$
--   \int_S f(z)\,dz=\int_s\left(\int_{[l(r),\,u(r)]}f(b,r)\,db\right)dr .
--   $$
--
--   Thus a region described by its horizontal slices (the slice at height $r$ is the closed interval $[l(r),u(r)]$ if $r\in s$ and empty otherwise) can be integrated slice by slice. This form of Fubini's theorem is used to compute areas of the cone-shaped planar regions of the singular covering construction, such as the triangles $\{0\le z_1\le a,\ |z_0|\le z_1\}$ and their truncations.
--
--   **Formalization Note** Integrals are Bochner integrals with respect to Lebesgue measure on `Plane` (Lean's Euclidean plane) and on the real line; the point $(b,r)$ is `vec2 b r`, and the inner integral is over `Icc (l r) (u r)`, which is empty when $l(r)>u(r)$. No measurability of $l$ and $u$ is assumed. In Lean a non-integrable function has integral $0$; since $f$ is integrable on $S$, the inner integrands are integrable for almost every $r$, so this convention does not affect the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/PlanarIntegration.lean#L69-L86

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

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.plane_setIntegral_horizontal_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 1 ∈ s ∧ z 0 ∈ Icc (l (z 1)) (u (z 1))) :
    (∫ z in S, f z) = ∫ r in s, ∫ b in Icc (l r) (u r), f (vec2 b r) := by sorry
