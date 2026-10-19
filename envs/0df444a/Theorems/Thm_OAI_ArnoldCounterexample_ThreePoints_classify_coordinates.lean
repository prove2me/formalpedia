-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_ThreePoints_classify_coordinates
-- name    : OAI.ArnoldCounterexample.ThreePoints.classify_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:34:05.908049+00:00
-- url     : https://prove2.me/theorems/87ff7464-1984-4cdb-965a-77f6f6790e07
-- title:
--   The Lagrange system on $S^2\times S^2$ has only the solutions $(p,-e)$ and the pair with $\mu^2=3$
-- statement:
--   Let $x=(x_0,x_1,x_2)$ and $y=(y_0,y_1,y_2)$ be real unit vectors, $|x|^2=|y|^2=1$, and let $\lambda,\mu\in\mathbb{R}$ satisfy
--   $$
--   (1+y_0,\ y_1,\ y_2)=\lambda\,(x_0,x_1,x_2),\qquad (x_0,\ x_1,\ x_2-1)=\mu\,(y_0,y_1,y_2).
--   $$
--   Then either
--   $$
--   x=(0,0,1),\quad y=(-1,0,0),
--   $$
--   or
--   $$
--   \mu^2=3,\quad x=\Bigl(\frac\mu2,0,-\frac12\Bigr),\quad y=\Bigl(\frac12,0,-\frac\mu2\Bigr).
--   $$
--
--   These equations are the Lagrange conditions for critical points of $f(x,y)=\langle x,y\rangle+x_0-y_2$ on $S^2\times S^2$. The classification shows that $f$ has exactly three critical points, which become the three fixed points of the counterexample map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/ThreePoints.lean#L37-L94

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

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.ThreePoints
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff

theorem OAI.ArnoldCounterexample.ThreePoints.classify_coordinates
    {x₀ x₁ x₂ y₀ y₁ y₂ lam μ : ℝ}
    (hx : x₀^2 + x₁^2 + x₂^2 = 1)
    (hy : y₀^2 + y₁^2 + y₂^2 = 1)
    (h₀ : 1 + y₀ = lam * x₀) (h₁ : y₁ = lam * x₁) (h₂ : y₂ = lam * x₂)
    (g₀ : x₀ = μ * y₀) (g₁ : x₁ = μ * y₁) (g₂ : x₂ - 1 = μ * y₂) :
    (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 1 ∧ y₀ = -1 ∧ y₁ = 0 ∧ y₂ = 0) ∨
    (μ^2 = 3 ∧ x₀ = μ/2 ∧ x₁ = 0 ∧ x₂ = -1/2 ∧
      y₀ = 1/2 ∧ y₁ = 0 ∧ y₂ = -μ/2) := by sorry
