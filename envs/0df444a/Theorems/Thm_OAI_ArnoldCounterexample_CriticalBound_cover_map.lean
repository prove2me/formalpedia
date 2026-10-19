-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_cover_map
-- name    : OAI.ArnoldCounterexample.CriticalBound.cover_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:26:01.637434+00:00
-- url     : https://prove2.me/theorems/d4e01ee6-a4e9-4937-a49f-3f5d375dc3a5
-- title:
--   At most three critical points give a nonvanishing phase-equivariant map $S\to\mathbb{C}^3$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $\pi:S\to Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$ is the projection. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0=\sum_jz_jv_j$. A function $h:Q_3\to\mathbb{R}$ is smooth if every $z\in S$ has an open neighbourhood $U\subseteq\mathbb{C}^5$ and a function $g$, smooth on $U$, with $g(y)=h(\pi y)$ for $y\in S\cap U$ (a local lift). A point $p\in Q_3$ is critical for $h$ if every local lift $g$ at every representative $z$ of $p$ has $dg(z)[v]=0$ for all horizontal $v$.
--
--   Let $h$ be a smooth function on $Q_3$ with at most three critical points. Then there is a smooth map $F:\mathbb{C}^5\to\mathbb{C}^3$ such that for all $z\in S$:
--   $$
--   F(z)\ne0,\qquad F(\alpha z)=\alpha\,F(z)\quad\text{for all }|\alpha|=1 .
--   $$
--
--   The number of critical points bounds the size of a Lusternik–Schnirelmann-type cover of $Q_3$. Each cover set contributes one complex coordinate of $F$. A topological argument will show that such an $F$ cannot exist, so every smooth function on $Q_3$ has at least four critical points.
--
--   **Formalization Note** The hypothesis is `(criticalSet h).encard ≤ 3`, with cardinality in $\mathbb{N}\cup\{\infty\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Deformation.lean#L156-L213

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
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms

theorem OAI.ArnoldCounterexample.CriticalBound.cover_map (h : SmoothFunction) (hsmall : (criticalSet h).encard ≤ 3) :
    ∃ F : CV → CSpace 3, ContDiff ℝ ∞ F ∧
      (∀ z : UnitQuadric, F z ≠ 0) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) := by sorry
