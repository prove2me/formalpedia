-- Prove2me | Theorems.Thm_OAI_Problem160_properColoring_seven_of_normalized_cover
-- name    : OAI.Problem160.properColoring_seven_of_normalized_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:42:06.356056+00:00
-- url     : https://prove2.me/theorems/2217c0c2-5387-43b2-b992-f3fc2a505645
-- title:
--   The covering bound for the triangular lattice yields a proper seven-coloring of the plane
-- statement:
--   Equip the plane $\mathbb{R}^2$ with the Euclidean distance. Assume the covering property of the unit triangular lattice: for all real numbers $x,y$ there are integers $a,b$ with
--   $$\Bigl(x-\bigl(a+\tfrac b2\bigr)\Bigr)^2+\Bigl(y-\tfrac{\sqrt3}{2}\,b\Bigr)^2\le\frac13 .$$
--   Then the plane admits a proper coloring with $7$ colors: there is a map $c:\mathbb{R}^2\to\{0,1,\dots,6\}$ such that
--   $$\forall\, p,q\in\mathbb{R}^2:\qquad \|p-q\|=1\ \Longrightarrow\ c(p)\ne c(q).$$
--   Points at distances other than $1$ may share a color, and no measurability or regularity of $c$ is required.
--
--   The theorem isolates the arithmetic and metric part of the classical seven-coloring of the plane built on the triangular lattice, leaving the elementary covering bound as its only geometric input. Since that hypothesis is true (every point of the plane lies within distance $1/\sqrt3$ of the unit triangular lattice), the two results together show that the chromatic number of the plane is at most $7$.
--
--   **Formalization Note** The conclusion is `ProperColoring 7`: there exists `c : Plane → Fin 7` with `dist x y = 1 → c x ≠ c y` for all `x y`, where `Plane` is `EuclideanSpace ℝ (Fin 2)`. The hypothesis `hcover` has exactly the form of the separately stated covering theorem for the triangular lattice, with `Real.sqrt 3` for $\sqrt3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Seven.lean#L14-L32

import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic
import Definitions.Def_OAI_Geometry_PlaneColoring_Metric
import Definitions.Def_OAI_Geometry_PlaneColoring_MeasurableProper

open OAI OAI.Problem160

theorem OAI.Problem160.properColoring_seven_of_normalized_cover
    (hcover : ∀ x y : ℝ, ∃ a b : ℤ,
      (x - ((a : ℝ) + (b : ℝ) / 2)) ^ 2 +
        (y - Real.sqrt 3 * b / 2) ^ 2 ≤ (1 / 3 : ℝ)) :
    ProperColoring 7 := by sorry
