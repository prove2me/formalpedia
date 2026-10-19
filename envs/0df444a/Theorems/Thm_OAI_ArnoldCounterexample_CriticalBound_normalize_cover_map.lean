-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_normalize_cover_map
-- name    : OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:26:41.441319+00:00
-- url     : https://prove2.me/theorems/80b58349-8fe9-4345-9a88-8cfe6605558d
-- title:
--   A nonvanishing equivariant map $S\to\mathbb{C}^3$ can be normalized to land in the unit sphere
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$ and $|z|^2=\sum_j|z_j|^2$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $\pi:S\to Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$ is the projection. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0=\sum_jz_jv_j$.
--
--   Let $F:\mathbb{C}^5\to\mathbb{C}^3$ be smooth, with $F(z)\ne0$ and $F(\alpha z)=\alpha F(z)$ for all $z\in S$ and $|\alpha|=1$. Then there is a smooth $F':\mathbb{C}^5\to\mathbb{C}^3$ such that for all $z\in S$:
--   $$
--   |F'(z)|^2=1,\qquad F'(\alpha z)=\alpha\,F'(z)\quad(|\alpha|=1).
--   $$
--
--   On $S$ the new map is $F/|F|$. The point is that it extends smoothly to all of $\mathbb{C}^5$, which the forms-based obstruction argument requires.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Deformation.lean#L215-L260

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

theorem OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map {F : CV → CSpace 3} (hF : ContDiff ℝ ∞ F)
    (hne : ∀ z : UnitQuadric, F z ≠ 0)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    ∃ F' : CV → CSpace 3, ContDiff ℝ ∞ F' ∧
      (∀ z : UnitQuadric, normSq 3 (F' z) = 1) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F' (a • (z : CV)) = a • F' z) := by sorry
