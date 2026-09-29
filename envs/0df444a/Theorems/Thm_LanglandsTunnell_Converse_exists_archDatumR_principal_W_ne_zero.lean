-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_principal_W_ne_zero
-- name    : LanglandsTunnell.Converse.exists_archDatumR_principal_W_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3bbd6b53-4c30-5eed-8380-f4c823aa99e6
-- title:
--   Non-vanishing archimedean Whittaker datum for real principal series
-- statement:
--   Let $u_1,u_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2\mathbb Z$, and let $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ be the corresponding real archimedean parameter. The assertion is that there exist a datum $D$ of type `ArchDatumR P` and an element $g\in\mathrm{GL}_2(\mathbb R)$ with $D.W\,g\neq 0$. Unfolding, such a datum consists of a function $W$ on $2\times 2$ real matrices which is $C^\infty$ on the set `glSet` of matrices of non-zero determinant, satisfies $W(\mathrm{unip}(x)\,g)=\psi(x)W(g)$ for the upper unipotent $\mathrm{unip}(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $W(z\cdot g)=\mathrm{centralChar}(P)(z)\,|z|\,W(g)$ for $z\neq0$; together with a function $\mathrm{zetaEntire}(g,u,a,\cdot)$, entire in the last variable, and a real abscissa such that, whenever $\det g\neq0$ and the abscissa is below $\mathrm{Re}(s)+\mathrm{Re}(u)$, the integrand $\mathrm{zetaIntegrand}\,W\,g\,u\,a\,s$ is integrable over $\mathbb R$ with integral equal to $\mathrm{archFactor}_{P.\mathrm{twist}(u,a)}(s)\cdot\mathrm{zetaEntire}(g,u,a,s)$, where $P.\mathrm{twist}(u,a)$ is the principal parameter $(u_1+u,a_1+a,u_2+u,a_2+a)$; the functional equation $\mathrm{zetaEntire}(\mathrm{weyl}\cdot g,-(u+u_1+u_2),a+a_1+a_2,1-s)=\varepsilon(P.\mathrm{twist}(u,a))\,\mathrm{zetaEntire}(g,u,a,s)$ for $\det g\neq0$; finite-order bounds $\|\mathrm{zetaEntire}(g,u,a,s)\|\le C e^{D|\mathrm{Im}\,s|}$ on every vertical strip; and, for each order $j$ of iterated derivative of $W$ within `glSet` evaluated at $\mathrm{diagOneMulCoords}\,y\,k$ with $k$ satisfying `IsK`, rapid decay $O(|y|^{-N})$ for $|y|\ge1$ and a bound $O(|y|^{-\sigma})$ for $0<|y|\le1$.
--
--   This provides the archimedean input at a real place for the principal-series case: the Jacquet Whittaker function of an induced representation of $\mathrm{GL}_2(\mathbb R)$, packaged with its local zeta integrals, gamma and epsilon factors and growth estimates, and shown not to vanish identically. It is the principal-series half of [`LanglandsTunnell.Converse.exists_archDatumR_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumR_W_ne_zero), which supplies the real archimedean local data used in the converse-theorem construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_archDatumR_principal_W_ne_zero.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_archDatumR_principal_W_ne_zero (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) :
    ∃ D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂), ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := by sorry
