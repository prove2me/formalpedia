-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_local_lift_derivative_eq
-- name    : OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:23:47.517312+00:00
-- url     : https://prove2.me/theorems/cf82f15d-5437-4ae5-95e6-e5fd544184dc
-- title:
--   All local lifts of a function on $Q_3$ have the same horizontal derivative
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $\pi:S\to Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$ is the projection. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0=\sum_jz_jv_j$. A function $h:Q_3\to\mathbb{R}$ is smooth if every $z\in S$ has an open neighbourhood $U\subseteq\mathbb{C}^5$ and a function $g$, smooth on $U$, with $g(y)=h(\pi y)$ for $y\in S\cap U$ (a local lift). A point $p\in Q_3$ is critical for $h$ if every local lift $g$ at every representative $z$ of $p$ has $dg(z)[v]=0$ for all horizontal $v$.
--
--   Let $h:Q_3\to\mathbb{R}$ and let $G:\mathbb{C}^5\to\mathbb{R}$ be a globally smooth function with $G(z)=h(\pi z)$ for all $z\in S$. Then for every $z\in S$, every local lift $g$ of $h$ at $z$, and every horizontal $v$ at $z$,
--   $$
--   dg(z)[v]=dG(z)[v].
--   $$
--
--   So the horizontal derivative of a function on $Q_3$ does not depend on the chosen extension. Criticality can therefore be tested with a single global extension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Deformation.lean#L40-L61

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ArnoldCounterexample.Quadric

theorem OAI.ArnoldCounterexample.CriticalBound.local_lift_derivative_eq {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (U : Set CV) (g : CV → ℝ)
    (hg : LocalFunctionLift h z U g) (v : CV) (hv : Horizontal z v) :
    fderiv ℝ g z v = fderiv ℝ G z v := by sorry
