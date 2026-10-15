-- Prove2me | Theorems.Thm_OAI_TriangularCovering_inv_sqrt_remainder
-- name    : OAI.TriangularCovering.inv_sqrt_remainder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:58:40.278418+00:00
-- url     : https://prove2.me/theorems/41e0804c-91df-48c2-b3d9-ab49e79750fa
-- title:
--   Quadratic remainder bound for the linear approximation of $1/\sqrt{1+x}$
-- statement:
--   For every real number $x\ge 0$,
--
--   $$
--   \left|\frac{1}{\sqrt{1+x}}-\Bigl(1-\frac{x}{2}\Bigr)\right|\le x^2 .
--   $$
--
--   Here $1-\frac x2$ is the first-order Taylor polynomial of $(1+x)^{-1/2}$ at $x=0$, and the inequality is a remainder bound with an explicit absolute constant that holds on the whole half-line $[0,\infty)$, not only asymptotically as $x\to 0$. Such a uniform bound is convenient when normalizing factors of the form $1/\sqrt{1+\varepsilon^2D}$ have to be expanded with fully explicit error terms, as in the asymptotic area estimates for coverings of the regular tetrahedron by triangular cylinders.
--
--   **Formalization Note** The left-hand side is `1 / Real.sqrt (1+x)`. Since $x\ge 0$, the square root is at least $1$, so no division-by-zero convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Asymptotics.lean#L11-L34

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
import Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.inv_sqrt_remainder {x : ℝ} (hx : 0 ≤ x) :
    |1 / Real.sqrt (1+x) - (1-x/2)| ≤ x^2 := by sorry
