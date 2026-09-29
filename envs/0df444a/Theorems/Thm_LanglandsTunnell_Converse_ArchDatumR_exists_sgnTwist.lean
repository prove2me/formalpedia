-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_sgnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/621ba74a-68eb-5609-8bce-6db0100e5bb4
-- title:
--   Sign-of-determinant twist shifts both parities of a principal-series archimedean datum
-- statement:
--   Let $u_1,u_2\in\mathbb{C}$ and let $a_1,a_2\in\mathbb{Z}/2$. Suppose $D$ is an archimedean datum for the real principal-series parameter $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, that is, a function $W\colon M_2(\mathbb{R})\to\mathbb{C}$ which is $C^\infty$ on the set of matrices of nonzero determinant, satisfies $W(n(x)g)=\psi(x)W(g)$ for $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and the central law $W(zg)=\omega_P(z)\,|z|\,W(g)$ for $z\neq 0$, together with the accompanying zeta package: a family $\zeta(g,u,a,s)$, entire in $s$, an abscissa beyond which the twisted zeta integrands of $W$ are integrable and their integrals equal $(\,P\text{ twisted by }(u,a)\,)$'s archimedean $\Gamma$-factor at $s$ times $\zeta(g,u,a,s)$, the local functional equation $\zeta(wg,-(u+u_1+u_2),a+a_1+a_2,1-s)=\varepsilon(P\text{ twisted by }(u,a))\,\zeta(g,u,a,s)$ for $w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $\det g\neq 0$, finite order of $\zeta$ in vertical strips, and the two decay bounds for all iterated derivatives of $W$ along the torus, at large and at small $|y|$. Then there is an archimedean datum $D'$ for the parameter $\mathrm{principal}\,u_1\,(a_1+1)\,u_2\,(a_2+1)$, with the same exponents and both parities shifted by $1$, whose Whittaker function is $g\mapsto \operatorname{sgn}(\det g)\cdot W(g)$, the sign being $0$ when $\det g=0$.
--
--   This is the archimedean local statement that multiplication by the sign character of the determinant carries a Whittaker datum of the real principal series $\pi(u_1,a_1;u_2,a_2)$ to one for $\pi(u_1,a_1+1;u_2,a_2+1)$, the central character and $\Gamma$- and $\varepsilon$-factors changing accordingly. It is used in the construction of an archimedean datum with prescribed weight character, minimal type, Casimir eigenvalue and nonvanishing Whittaker function, within the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.exists_sgnTwist (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) :
    ∃ D' : ArchDatumR (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)),
      D'.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D.W g := by sorry
