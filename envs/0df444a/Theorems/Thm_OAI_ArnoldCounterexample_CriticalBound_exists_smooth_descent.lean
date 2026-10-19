-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_exists_smooth_descent
-- name    : OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:24:26.637056+00:00
-- url     : https://prove2.me/theorems/47a32b14-f3f5-4adf-9bed-9ede382568ab
-- title:
--   A smooth phase-equivariant descent map for any smooth function on $Q_3$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $\pi:S\to Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$ is the projection. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0=\sum_jz_jv_j$. A function $h:Q_3\to\mathbb{R}$ is smooth if every $z\in S$ has an open neighbourhood $U\subseteq\mathbb{C}^5$ and a function $g$, smooth on $U$, with $g(y)=h(\pi y)$ for $y\in S\cap U$ (a local lift). A point $p\in Q_3$ is critical for $h$ if every local lift $g$ at every representative $z$ of $p$ has $dg(z)[v]=0$ for all horizontal $v$.
--
--   Let $h:Q_3\to\mathbb{R}$ and let $G:\mathbb{C}^5\to\mathbb{R}$ be smooth with $G(z)=h(\pi z)$ on $S$. Then there is a smooth map $D:\mathbb{C}^5\to\mathbb{C}^5$ such that for all $z\in S$:
--
--   1. $D(z)\in S$;
--   2. $D(\alpha z)=\alpha D(z)$ for every $\alpha\in\mathbb{C}$ with $|\alpha|=1$;
--   3. and 4. the descent property
--   $$
--   G\bigl(D(z)\bigr)\le G(z),\qquad G\bigl(D(z)\bigr)=G(z)\ \Longrightarrow\ \pi(z)\ \text{is a critical point of } h .
--   $$
--
--   $D$ descends to a continuous map of $Q_3$ that never increases $h$ and moves every non-critical point strictly downhill. No nondegeneracy (Morse) assumption is needed, and no existence theorem for gradient flows is used. This is the deformation step of the critical-point lower bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Deformation.lean#L80-L110

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

theorem OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z)) :
    ∃ D : CV → CV, ContDiff ℝ ∞ D ∧
      (∀ z : UnitQuadric, IsUnitQuadric (D z)) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → D (a • (z : CV)) = a • D z) ∧
      (∀ z : UnitQuadric, G (D z) ≤ G z) ∧
      (∀ z : UnitQuadric, G (D z) = G z → IsCritical h (project z)) := by sorry
