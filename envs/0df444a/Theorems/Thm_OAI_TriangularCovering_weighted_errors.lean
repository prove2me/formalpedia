-- Prove2me | Theorems.Thm_OAI_TriangularCovering_weighted_errors
-- name    : OAI.TriangularCovering.weighted_errors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:46:31.976846+00:00
-- url     : https://prove2.me/theorems/f1ad26ec-1ba7-4abb-8648-ca05fa23d6cd
-- title:
--   Two errors of size $\Delta/4$ with weights of total size at most one contribute at most $\varepsilon\Delta/4$
-- statement:
--   Let $\varepsilon\ge0$, $\Delta\ge0$, and let $x,y,e,f$ be real numbers with
--   $$
--   |x|+|y|\le1,\qquad |e|\le\frac\Delta4,\qquad |f|\le\frac\Delta4 .
--   $$
--   Then
--   $$
--   -\varepsilon xe+\varepsilon yf\le\frac{\varepsilon\Delta}{4}.
--   $$
--
--   The lemma bounds a linear combination of two error terms whose weights $x,y$ have $\ell^1$-norm at most $1$. In the covering of the tetrahedron by tilted triangular cylinders, $(x,y)$ are the horizontal coordinates of a point of the tetrahedron, so $|x|+|y|\le1$, and $e,f$ are discretization errors of tilt coefficients. The radial exclusion estimate uses the lemma twice: with $\Delta=2$ for a crude a priori bound, and with $\Delta$ equal to the mesh width.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L190-L204

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.weighted_errors {ε Δ x y e f : ℝ} (he : 0 ≤ ε) (hΔ : 0 ≤ Δ)
    (hxy : |x| + |y| ≤ 1) (he' : |e| ≤ Δ / 4) (hf : |f| ≤ Δ / 4) :
    -ε * x * e + ε * y * f ≤ ε * Δ / 4 := by sorry
