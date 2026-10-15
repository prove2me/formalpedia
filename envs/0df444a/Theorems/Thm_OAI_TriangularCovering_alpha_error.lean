-- Prove2me | Theorems.Thm_OAI_TriangularCovering_alpha_error
-- name    : OAI.TriangularCovering.alpha_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:44:52.914603+00:00
-- url     : https://prove2.me/theorems/0158ce8d-890f-4862-94fe-1130016b7771
-- title:
--   The secant coefficient $\alpha(a,b)$ approximates $(1+q^2)/4$ on the cell $[a,b]$
-- statement:
--   Let $\alpha(a,b)=\frac{1+ab}{4}$. Let $a,b,q$ be real numbers with $|a|\le1$, $|q|\le1$ and $a\le q\le b$. Then
--   $$
--   \left|\alpha(a,b)-\frac{1+q^2}{4}\right|\le\frac{b-a}{2}.
--   $$
--
--   No bound on $b$ is assumed beyond $q\le b$. In the covering of the tetrahedron by tilted triangular cylinders, $[a,b]$ is a mesh cell of $[-1,1]$ and $q$ is the angular coordinate of a point in that cell; the lemma says that the secant coefficient $\alpha(a,b)$ differs from its pointwise limit $(1+q^2)/4$ by at most half the mesh width. This error bound is one of the inputs of the radial exclusion estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L99-L113

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.alpha_error {a b q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1)
    (haq : a ≤ q) (hqb : q ≤ b) :
    |alpha a b - (1 + q ^ 2) / 4| ≤ (b - a) / 2 := by sorry
