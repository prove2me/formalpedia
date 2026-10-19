-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Field_core_homogeneous
-- name    : OAI.ArnoldCounterexample.Field.core_homogeneous
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:35:12.832981+00:00
-- url     : https://prove2.me/theorems/8519ece6-331e-4d09-8b84-172c2f362d8d
-- title:
--   The Hamiltonian field is complex-homogeneous of degree one along rays through the fixed quadric
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$. Let $p_{ab}(z)=2\operatorname{Im}(\bar z_az_b)$, and let $L,R:\mathbb{C}^5\to\mathbb{R}^3$ be the sphere factors $L=(p_{12}+p_{34},p_{13}-p_{24},p_{14}+p_{23})$ and $R=(p_{12}-p_{34},p_{13}+p_{24},p_{14}-p_{23})$. Let $Y$ be the Hamiltonian vector field of the potential $K=L_0-R_2+b(|L|^2)\langle L,R\rangle$, where $b$ is smooth with $b(s)=s^{-1/2}$ for $s\in[\tfrac1{32},32]$.
--
--   Let $z\in S$ with $z_0=0$, and let $c\in\mathbb{C}$ with $\tfrac12<|c|^2<2$. Then
--   $$
--   Y(c\,z)=c\,Y(z).
--   $$
--
--   Although $Y$ is not linear, it behaves linearly along complex rays through the fixed quadric $\{z_0=0\}$ within this range of scales. This is what allows the implicit midpoint equations at a fixed point to be solved explicitly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/FieldAlgebra.lean#L41-L54

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Field
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology Matrix
open Set Filter

theorem OAI.ArnoldCounterexample.Field.core_homogeneous (z : UnitQuadric) (hz : (z:CV) 0 = 0) (c : ℂ)
    (hc : Complex.normSq c ∈ Ioo (1/2:ℝ) 2) : core (c • (z:CV)) = c • core z := by sorry
