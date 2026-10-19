-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_rotationDerivative_phase
-- name    : OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:20:57.004274+00:00
-- url     : https://prove2.me/theorems/0197cf2d-a68b-4a09-940d-55512382cbda
-- title:
--   Rotation derivatives of a phase-invariant function are phase invariant on the unit quadric
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}=S/U(1)$. Let $R_{ab}=E_{ba}-E_{ab}$ be the elementary skew matrix rotating the $(a,b)$ plane, acting on $\mathbb{C}^5$ by matrix multiplication. Let $G:\mathbb{C}^5\to\mathbb{R}$ be smooth with $G(\alpha z)=G(z)$ for all $z\in S$ and $|\alpha|=1$, and write $\partial_{ab}G(z)=dG(z)[R_{ab}z]$. Then for every $z\in S$, every unit scalar $\alpha$ and all $a,b$,
--   $$
--   \partial_{ab}G(\alpha z)=\partial_{ab}G(z).
--   $$
--
--   The rotation derivatives of a function that descends to $Q_3$ therefore descend as well. This makes the squared rotation gradient a well-defined function on $Q_3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Coordinates.lean#L126-L143

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open ArnoldCounterexample.Forms
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_2

theorem OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) (i j : Fin 5) :
    rotationDerivative G i j (a • (z : CV)) = rotationDerivative G i j z := by sorry
