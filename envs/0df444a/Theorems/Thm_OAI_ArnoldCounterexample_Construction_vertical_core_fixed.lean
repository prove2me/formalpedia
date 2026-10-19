-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Construction_vertical_core_fixed
-- name    : OAI.ArnoldCounterexample.Construction.vertical_core_fixed
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:45:19.607977+00:00
-- url     : https://prove2.me/theorems/b2549a22-cd5a-4c06-9fc7-b7a2da05bd8b
-- title:
--   Where the Hamiltonian field is a small rotation of $z$, the point is fixed by the counterexample map
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$. Let $p_{ab}(z)=2\operatorname{Im}(\bar z_az_b)$, and let $L,R:\mathbb{C}^5\to\mathbb{R}^3$ be the sphere factors $L=(p_{12}+p_{34},p_{13}-p_{24},p_{14}+p_{23})$ and $R=(p_{12}-p_{34},p_{13}+p_{24},p_{14}-p_{23})$. Let $Y$ be the Hamiltonian vector field of the potential $K=L_0-R_2+b(|L|^2)\langle L,R\rangle$, where $b$ is smooth with $b(s)=s^{-1/2}$ for $s\in[\tfrac1{32},32]$. Let $\varphi:Q_3\to Q_3$ be the counterexample map, $\varphi([z])=[F(1,z)]$. Here $F(1,\cdot)=\iota\circ F_{\mathrm{mid}}(1,\cdot)$ is the coordinate involution $\iota(z)=(z_0,-z_1,\dots,-z_4)$ after one implicit-midpoint step $F_{\mathrm{mid}}(1,z)=2c-z$. The centre $c$ solves $c=z+\varepsilon X(c)$, where $X$ is the compactly supported field agreeing with $Y$ for $|c|^2<4$, and $\varepsilon>0$ is the small step size.
--
--   Let $z\in S$ with $z_0=0$, and suppose $Y(z)=b\,iz$ for a real number $b$ with $|b|\le3$. Then
--   $$
--   \varphi([z])=[z].
--   $$
--
--   This is the converse direction of the fixed-point analysis. Lifts of critical points at which the field is a vertical (phase) direction of moderate size give fixed points of $\varphi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/FixedPoints.lean#L103-L166

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

theorem OAI.ArnoldCounterexample.Construction.vertical_core_fixed (z : UnitQuadric) (hz0 : (z:CV) 0 = 0) (b : ℝ)
    (hb : |b| ≤ 3) (hcore : core z = b • (Complex.I • (z:CV))) :
    mainEquiv (project z) = project z := by sorry
