-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_ThreePoints_multiplierCritical_iff
-- name    : OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:34:37.063987+00:00
-- url     : https://prove2.me/theorems/686ca636-aba1-4f8e-966d-aac76043e079
-- title:
--   The function $\langle x,y\rangle+x_0-y_2$ on $S^2\times S^2$ has exactly three critical points
-- statement:
--   On $S^2\times S^2\subset\mathbb{R}^3\times\mathbb{R}^3$, call $(x,y)$ multiplier-critical if there are $\lambda,\mu\in\mathbb{R}$ with
--   $$
--   (1+y_0,y_1,y_2)=\lambda x,\qquad (x_0,x_1,x_2-1)=\mu y,
--   $$
--   the Lagrange conditions for $f(x,y)=\langle x,y\rangle+x_0-y_2$. Then $(x,y)$ is multiplier-critical if and only if it is one of
--   $$
--   q_0=\bigl((0,0,1),(-1,0,0)\bigr),\quad q_+=\Bigl(\bigl(\tfrac{\sqrt3}2,0,-\tfrac12\bigr),\bigl(\tfrac12,0,-\tfrac{\sqrt3}2\bigr)\Bigr),\quad q_-=\Bigl(\bigl(-\tfrac{\sqrt3}2,0,-\tfrac12\bigr),\bigl(\tfrac12,0,\tfrac{\sqrt3}2\bigr)\Bigr).
--   $$
--
--   This complete list, including the degenerate critical point $q_0$, is what makes the fixed set of the counterexample map have exactly three points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/ThreePoints.lean#L110-L131

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

theorem OAI.ArnoldCounterexample.ThreePoints.multiplierCritical_iff (q : Pair) :
    MultiplierCritical q ↔ q = qzero ∨ q = qplus ∨ q = qminus := by sorry
