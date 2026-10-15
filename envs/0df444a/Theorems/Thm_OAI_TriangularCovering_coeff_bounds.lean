-- Prove2me | Theorems.Thm_OAI_TriangularCovering_coeff_bounds
-- name    : OAI.TriangularCovering.coeff_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:43:37.866115+00:00
-- url     : https://prove2.me/theorems/fb253e73-5ab8-4f66-a876-100f7ae4620b
-- title:
--   Range bounds for the secant coefficients and the cutoff coefficient on $[-1,1]$
-- statement:
--   Let $\eta=1/1000$ and, for real $a,b,q$,
--   $$
--   \alpha(a,b)=\frac{1+ab}{4},\qquad \beta(a,b)=\frac{a+b}{4},\qquad d(q)=\frac{q^2(1+q^2)}{16},\qquad M(a,b)=\eta+\max\{d(a),d(b)\}.
--   $$
--   If $|a|\le1$ and $|b|\le1$, then:
--
--   1. $0\le\alpha(a,b)\le\frac12$;
--   2. $|\beta(a,b)|\le\frac12$;
--   3. $\eta\le M(a,b)\le\frac18+\eta$.
--
--   These are uniform bounds on the coefficients attached to a mesh cell $[a,b]\subseteq[-1,1]$ in the covering of the tetrahedron by tilted triangular cylinders: $\alpha$ and $\beta$ determine the tilt of the cylinder axes, and $M$ is the second-order correction in the cutoff height $\frac12+\varepsilon^2M(a,b)$. They provide the a priori ranges required by the radial exclusion estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L66-L85

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.coeff_bounds {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 / 2 ∧ |beta a b| ≤ 1 / 2 ∧
    η ≤ cutoffCoeff a b ∧ cutoffCoeff a b ≤ 1 / 8 + η := by sorry
