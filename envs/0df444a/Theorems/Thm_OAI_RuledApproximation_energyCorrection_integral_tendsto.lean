-- Prove2me | Theorems.Thm_OAI_RuledApproximation_energyCorrection_integral_tendsto
-- name    : OAI.RuledApproximation.energyCorrection_integral_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:22:04.385852+00:00
-- url     : https://prove2.me/theorems/e2ddd48a-d991-4b51-9449-a60c5015387e
-- title:
--   Limit of the integrated second-order weight correction over the singular domain
-- statement:
--   Let $V_p$ be the singular field
--
--   $$
--   V_p(z)=\Big(\tfrac14\,(2z_1)^{p-1}\Big(p+(2-p)\,\frac{z_0^2}{z_1^2}\Big),\ \ (2z_1)^{p-2}\,z_0\Big),\qquad z=(z_0,z_1),
--   $$
--
--   with components $V_p(z)_0,V_p(z)_1$. Define the energy $H_p(z)=V_p(z)_0^2+2\,V_p(z)_1^2\ge0$ and, for $c\in\mathbb{R}$, the correction
--
--   $$
--   E_{p,c}(z)=-\frac{H_p(z)}{\sqrt{1+c^2H_p(z)}\,\Big(\sqrt{1+c^2H_p(z)}+1\Big)} .
--   $$
--
--   Let $\Omega_{p,\gamma,c}$ be the singular base domain, consisting of the points $b$ with $c^\gamma\le b_1\le2$, $|b_0|\le b_1$ and $b_1\le\tfrac12+c^2\Delta_p(b_0)+c^{5/2}$, where $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$, and let $T_{1/2}=\{(z_0,z_1):\ 0\le z_1\le\tfrac12,\ |z_0|\le z_1\}$.
--
--   **Theorem.** Let $1<p\le2$ and $\gamma>0$. Then
--
--   $$
--   \lim_{c\to0^+}\int_{\Omega_{p,\gamma,c}}E_{p,c}(z)\,dz=-\frac12\int_{T_{1/2}}H_p(z)\,dz .
--   $$
--
--   The correction is chosen so that
--
--   $$
--   \frac1{\sqrt{1+c^2V_p(z)_0^2+2c^2V_p(z)_1^2}}=\frac1{\sqrt{1+c^2H_p(z)}}=1+c^2E_{p,c}(z),
--   $$
--
--   where the left side is the weight of the tilted ruling direction $c\,V_p(z)$ in the physical coordinates with vertical scale $\sqrt2$. Integrating over the base domain, the weighted cost of a ruled family is the area of $\Omega_{p,\gamma,c}$ plus $c^2\int_{\Omega_{p,\gamma,c}}E_{p,c}$, so the theorem identifies the contribution of the tilt to the $c^2$ term in the cost expansion of the singular covering of the regular tetrahedron.
--
--   **Formalization Note** $H_p$ and $E_{p,c}$ are `singularEnergy p` and `energyCorrection p c`, and the domains are `singularDomain p gamma c` and `coneTriangle (1/2)`. The integrals are Bochner integrals for Lebesgue measure on `Plane`, and the limit is taken along the filter `𝓝[>] 0`. The field is given by its formula at every point; it vanishes at the origin for $p>1$, the only point of $T_{1/2}$ with $z_1=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularEnergy.lean#L147-L195

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
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.energyCorrection_integral_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 0 < gamma) :
    Tendsto (fun c : ℝ => ∫ z in singularDomain p gamma c, energyCorrection p c z) (𝓝[>] 0)
      (𝓝 (-(∫ z in coneTriangle (1/2), singularEnergy p z)/2)) := by sorry
