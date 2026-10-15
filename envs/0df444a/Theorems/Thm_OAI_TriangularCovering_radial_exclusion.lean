-- Prove2me | Theorems.Thm_OAI_TriangularCovering_radial_exclusion
-- name    : OAI.TriangularCovering.radial_exclusion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:47:06.203947+00:00
-- url     : https://prove2.me/theorems/b65f80c7-b4d7-463e-a188-03f2c0639ae8
-- title:
--   Radial exclusion: a point cannot lie beyond both the lower and the upper cutoff
-- statement:
--   Let $\eta=1/1000$ and $d(q)=q^2(1+q^2)/16$. Let $\varepsilon,\Delta,x,y,q,p,a,b,\beta,\gamma,M,N,r,s$ be real numbers satisfying the following hypotheses.
--
--   - Small parameters: $0<\varepsilon\le\eta/2$ and $0\le\Delta\le\varepsilon^2$.
--   - Ranges: $|x|+|y|\le1$, $|q|\le1$, $|p|\le1$, $0\le a\le\frac12$, $0\le b\le\frac12$, $|\beta|\le\frac12$, $|\gamma|\le\frac12$.
--   - Coefficient errors: $|\beta-\frac q2|\le\frac\Delta4$, $|\gamma-\frac p2|\le\frac\Delta4$, $|a-\frac{1+q^2}{4}|\le\frac\Delta2$ and $|b-\frac{1+p^2}{4}|\le\frac\Delta2$.
--   - Cutoff coefficients: $\eta+d(q)\le M$, $\eta+d(p)\le N$ and $M+N\le\frac14+2\eta$.
--   - Coordinate relations:
--   $$
--   r+s=1-\varepsilon x\beta+\varepsilon y\gamma,\qquad y=rq+\varepsilon xa,\qquad x=sp-\varepsilon yb .
--   $$
--
--   Then
--   $$
--   r\le\frac12+\varepsilon^2M\qquad\text{or}\qquad s\le\frac12+\varepsilon^2N .
--   $$
--
--   In the covering of the tetrahedron $\{(x,y,\sqrt2t):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$ by tilted triangular cylinders, $r$ and $s$ are the radial coordinates of a point measured from the bottom edge and from the top edge along the axes of a lower and an upper cylinder, $q$ and $p$ are the corresponding angular coordinates in mesh cells of width $\Delta$, the numbers $a,b,\beta,\gamma$ are the tilt coefficients of these cells, and $\frac12+\varepsilon^2M$, $\frac12+\varepsilon^2N$ are the cylinder heights. The conclusion says that a point cannot lie beyond both heights, so it is covered by the lower or by the upper cylinder. The constants are uniform: the mesh enters only through $\Delta\le\varepsilon^2$.
--
--   **Formalization Note** The real number $N$ in this statement is unrelated to the number of mesh cells used elsewhere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L259-L304

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.radial_exclusion {ε Δ x y q p a b β γ M N r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (hxy : |x| + |y| ≤ 1) (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (hβ : |β| ≤ 1 / 2) (hγ : |γ| ≤ 1 / 2)
    (heβ : |β - q / 2| ≤ Δ / 4) (heγ : |γ - p / 2| ≤ Δ / 4)
    (hea : |a - (1 + q ^ 2) / 4| ≤ Δ / 2)
    (heb : |b - (1 + p ^ 2) / 4| ≤ Δ / 2)
    (hM : η + d q ≤ M) (hN : η + d p ≤ N)
    (hMN : M + N ≤ 1 / 4 + 2 * η)
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    r ≤ 1 / 2 + ε ^ 2 * M ∨ s ≤ 1 / 2 + ε ^ 2 * N := by sorry
