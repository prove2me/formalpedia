-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_W_ne_zero
-- name    : LanglandsTunnell.Converse.exists_archDatumR_W_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c2880a8e-7836-574c-9325-b2f5b3d5c3a3
-- title:
--   Existence of a non-zero archimedean Whittaker datum at every real parameter
-- statement:
--   Let $P$ be an archimedean $\mathrm{GL}_2$ parameter at a real place, i.e. an element of `RealArchParam`: either `principal u₁ a₁ u₂ a₂` with $u_1,u_2\in\mathbb{C}$ and $a_1,a_2\in\mathbb{Z}/2$, or `discrete u k hk` with $u\in\mathbb{C}$ and $k\ge 1$. The assertion is that there exist a datum $D$ of type `ArchDatumR P` and an element $g$ of $\mathrm{GL}_2(\mathbb{R})$ with $D.W\,g\neq 0$ (the matrix underlying $g$ being fed to $D.W$). Here a term of `ArchDatumR P` consists of a function $W$ on real $2\times 2$ matrices that is $C^\infty$ on the set `glSet` of matrices of non-zero determinant, satisfies $W(\mathrm{unip}(x)g)=\psi(x)\,W(g)$ for $\mathrm{unip}(x)=\binom{1\;x}{0\;1}$ and $W(zg)=\mathrm{centralChar}\,P(z)\,|z|\,W(g)$ for $z\neq 0$, together with a family $\zeta(g,u,a,s)$ entire in $s$, an abscissa $\sigma_0$, integrability of the associated integrand and the identity $\int_{\mathbb{R}}\mathrm{zetaIntegrand}\,W\,g\,u\,a\,s\,(y)\,dy=\mathrm{archFactor}(P.\mathrm{twist}\,u\,a)(s)\cdot\zeta(g,u,a,s)$ for $\det g\neq 0$ and $\sigma_0<\mathrm{Re}(s+u)$, the functional equation $\zeta(wg,-(u+P.\mathrm{centralExponent}),a+P.\mathrm{centralSign},1-s)=\mathrm{epsilonFactor}(P.\mathrm{twist}\,u\,a)\cdot\zeta(g,u,a,s)$ with $w=\binom{0\;\;1}{-1\,0}$, finite order of $\zeta$ in vertical strips, and, for each order of differentiation, rapid decay of the derivatives of $W$ at $\mathrm{diag}(y,1)k$ with $k$ in `IsK` for $|y|\ge 1$ and a bound $C|y|^{-\sigma}$ for $0<|y|\le 1$.
--
--   This is the archimedean input to the converse-theorem construction: the existence of a Whittaker function at a real place with the prescribed unipotent and central transformation laws, growth and decay, and local gamma- and epsilon-factor functional equation, non-vanishing somewhere on the group. Since `ArchDatumR P` is satisfied by the zero function, the content lies in the non-vanishing clause; the statement is used by [`LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic`](thm.html#LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_forall_isNicePinned_of_centralChar_of_generic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_archDatumR_W_ne_zero.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_archDatumR_W_ne_zero (P : RealArchParam) :
    ∃ D : ArchDatumR P, ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := by sorry
