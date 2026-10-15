-- Prove2me | Theorems.Thm_OAI_TriangularCovering_finite_coordinate_cover
-- name    : OAI.TriangularCovering.finite_coordinate_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:49:14.739603+00:00
-- url     : https://prove2.me/theorems/0e531635-12a8-4fbd-ab7c-58e2c134388f
-- title:
--   Every point of the tetrahedron satisfies a lower or an upper sector-and-cutoff condition
-- statement:
--   Let $\eta=1/1000$ and use the notation $\alpha(a,b)=\frac{1+ab}4$, $\beta(a,b)=\frac{a+b}4$, $d(q)=\frac{q^2(1+q^2)}{16}$, $M(a,b)=\eta+\max\{d(a),d(b)\}$ and $T_\varepsilon(a,b)=\frac12+\varepsilon^2M(a,b)$. For $N\ge1$ let $h_N=2/N$ and $m_{N,j}=-1+j\,h_N$ be the uniform mesh of $[-1,1]$.
--
--   Let $N\ge1$ and $0<\varepsilon\le\eta/2$ with $h_N\le\varepsilon^2$, and let $x,y,t\in\mathbb{R}$ satisfy $|x|\le1-t$ and $|y|\le t$. Then at least one of the following holds.
--
--   1. (Lower hit.) There is $j\in\{0,\dots,N-1\}$ such that, with $a=m_{N,j}$, $b=m_{N,j+1}$, $\rho=t-\varepsilon x\,\beta(a,b)$ and $Y=y-\varepsilon x\,\alpha(a,b)$,
--   $$
--   0\le\rho\le T_\varepsilon(a,b)\qquad\text{and}\qquad a\rho\le Y\le b\rho .
--   $$
--   2. (Upper hit.) There is $j\in\{0,\dots,N-1\}$ such that, with $a=m_{N,j}$, $b=m_{N,j+1}$, $\sigma=1-t+\varepsilon y\,\beta(a,b)$ and $X=x+\varepsilon y\,\alpha(a,b)$,
--   $$
--   0\le\sigma\le T_\varepsilon(a,b)\qquad\text{and}\qquad a\sigma\le X\le b\sigma .
--   $$
--
--   The hypotheses on $x,y,t$ say exactly that $(x,y,\sqrt2t)$ lies in the regular tetrahedron $K=\{(x,y,\sqrt2t):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$; they force $0\le t\le1$. Condition 1 is the coordinate form of membership of this point in the $j$-th lower cylinder, which has direction $(1,\varepsilon\alpha,\sqrt2\varepsilon\beta)$ and is built on the triangle with vertices $(0,0,0)$, $(0,aT,\sqrt2T)$, $(0,bT,\sqrt2T)$, where $T=T_\varepsilon(a,b)$. Condition 2 is membership in the $j$-th upper cylinder, with direction $(-\varepsilon\alpha,1,\sqrt2\varepsilon\beta)$ and base triangle $(0,0,\sqrt2)$, $(aT,0,\sqrt2(1-T))$, $(bT,0,\sqrt2(1-T))$. Thus the theorem is the coordinate core of the fact that these $2N$ cylinders cover every point of $K$, boundary points included.
--
--   **Formalization Note** Conditions 1 and 2 are `LowerHit N j ε x y t` and `UpperHit N j ε x y t`, each a conjunction of `Sector` and a cutoff inequality; $h_N$ is `step N` and the cutoff is `cutoff ε a b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L447-L466

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.finite_coordinate_cover {N : ℕ} {ε x y t : ℝ}
    (hN : 0 < N) (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hmesh : step N ≤ ε ^ 2)
    (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < N ∧ LowerHit N j ε x y t) ∨
    (∃ j : ℕ, j < N ∧ UpperHit N j ε x y t) := by sorry
