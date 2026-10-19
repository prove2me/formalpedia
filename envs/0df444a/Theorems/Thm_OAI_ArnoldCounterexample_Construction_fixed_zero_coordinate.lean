-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Construction_fixed_zero_coordinate
-- name    : OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:39:16.242451+00:00
-- url     : https://prove2.me/theorems/d765b0d1-8084-4982-836d-3fd95ffd95ba
-- title:
--   Fixed points of the counterexample map lie on the hyperplane $z_0=0$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$. Let $\varphi:Q_3\to Q_3$ be the counterexample map, $\varphi([z])=[F(1,z)]$. Here $F(1,\cdot)=\iota\circ F_{\mathrm{mid}}(1,\cdot)$ is the coordinate involution $\iota(z)=(z_0,-z_1,\dots,-z_4)$ after one implicit-midpoint step $F_{\mathrm{mid}}(1,z)=2c-z$. The centre $c$ solves $c=z+\varepsilon X(c)$, where $X$ is the compactly supported field agreeing with $Y$ for $|c|^2<4$, and $\varepsilon>0$ is the small step size.
--
--   If $z\in S$ and $\varphi([z])=[z]$, then
--   $$
--   z_0=0 .
--   $$
--
--   All fixed points of $\varphi$ therefore lie on the quadric $\{z_0=0\}\cong S^2\times S^2$ fixed by the involution, where they can be compared with critical points of a function on $S^2\times S^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/FixedPoints.lean#L21-L43

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Construction
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

theorem OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    (z:CV) 0 = 0 := by sorry
