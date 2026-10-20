-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Construction_core_otherVector
-- name    : OAI.ArnoldCounterexample.Construction.core_otherVector
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:46:54.698806+00:00
-- url     : https://prove2.me/theorems/4dcaf4ca-eb5f-4aa2-84f8-066d2f342da8
-- title:
--   At the lifts $\zeta(\pm\sqrt3)$ the Hamiltonian field is the phase direction $-\tfrac{3r}{2}\,i\zeta$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$. Let $p_{ab}(z)=2\operatorname{Im}(\bar z_az_b)$, and let $L,R:\mathbb{C}^5\to\mathbb{R}^3$ be the sphere factors $L=(p_{12}+p_{34},p_{13}-p_{24},p_{14}+p_{23})$ and $R=(p_{12}-p_{34},p_{13}+p_{24},p_{14}-p_{23})$. Let $Y$ be the Hamiltonian vector field of the potential $K=L_0-R_2+b(|L|^2)\langle L,R\rangle$, where $b$ is smooth with $b(s)=s^{-1/2}$ for $s\in[\tfrac1{32},32]$.
--
--   For $r\in\mathbb{R}$ let $\zeta(r)=\bigl(0,\tfrac{1+r}4,\tfrac i2,\tfrac{1-r}4,-\tfrac i2\bigr)$. If $r^2=3$, then
--   $$
--   Y\bigl(\zeta(r)\bigr)=-\frac{3r}{2}\,i\,\zeta(r).
--   $$
--
--   Since $|3r/2|=\tfrac{3\sqrt3}{2}\le3$, the lifts $\zeta(\pm\sqrt3)$ of the critical points $q_\pm$ satisfy the hypothesis of the vertical-field criterion, and so they are fixed points of the counterexample map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/CriticalLifts.lean#L67-L81

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter
import Definitions.Def_OAI_Geometry_Arnold_Quotient
import Definitions.Def_OAI_Geometry_Arnold_Hamiltonian
import Definitions.Def_OAI_Geometry_Arnold_CriticalLifts

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Construction
universe uα
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

theorem OAI.ArnoldCounterexample.Construction.core_otherVector (r : ℝ) (hr : r^2 = 3) :
    core (otherVector r) = (-(3*r/2)) • (Complex.I • otherVector r) := by sorry
