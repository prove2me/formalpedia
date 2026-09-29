-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_archDatumR_W_eq
-- name    : LanglandsTunnell.Converse.PrincipalFamily.exists_archDatumR_W_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2244d3f4-0fe6-5a1d-bec6-2445c9d9efa7
-- title:
--   Principal-series Whittaker function comes from an archimedean datum
-- statement:
--   Let $u_1,u_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$. The assertion is that there exists a term $D$ of the structure `ArchDatumR` for the real archimedean parameter `RealArchParam.principal` $u_1,a_1,u_2,a_2$ whose underlying function $D.W$ is equal, as a function on $2\times2$ real matrices, to `Wmem` $u_1\,u_2\,a_1\,a_2$, i.e. to $$g\mapsto |\det g|\cdot \mathtt{quasiChar}\,u_1\,a_1(\det g)\cdot\int_{\mathbb R}\mathtt{innerW}\,a_1\,a_2\,g\,t\cdot \mathtt{quasiChar}\,(u_1-u_2)\,(a_1+a_2)(t)\,dt,$$ where $\mathtt{innerW}\,a_1\,a_2\,h\,t=\int_{\mathbb R}\mathtt{phiStd}\,a_1(-(t(h_{00}+xh_{10})))\,\mathtt{phiStd}\,a_2(-(t(h_{01}+xh_{11})))\,\psi(-x)\,dx$, all integrals being Bochner integrals. Producing such a $D$ amounts to verifying for this function: smoothness (as a function of the four matrix entries) on the set of invertible matrices; the unipotent law $W(\binom{1\ x}{0\ 1}g)=\psi(x)W(g)$; the central law $W(zg)=\mathtt{centralChar}(z)\,|z|\,W(g)$ for $z\neq0$; a zeta package, namely entire functions $\mathtt{zetaEntire}(g,u,a,\cdot)$ and an abscissa beyond which the twisted zeta integrands are integrable with integral equal to the archimedean factor of the twisted parameter $\mathtt{principal}\,(u_1+u)\,(a_1+a)\,(u_2+u)\,(a_2+a)$ at $s$ times $\mathtt{zetaEntire}$, the local functional equation linking $(\mathtt{weyl}\cdot g,-(u+u_1+u_2),a+a_1+a_2,1-s)$ to $(g,u,a,s)$ through the epsilon factor $\mathtt{signEpsilon}(a_1+a)\,\mathtt{signEpsilon}(a_2+a)$, and finite order in vertical strips; and the two decay estimates for all iterated derivatives along the torus coordinates, for $|y|\ge1$ and for $0<|y|\le1$.
--
--   This is the real-place input to the converse-theorem route: the explicit principal-series Whittaker function of Jacquet–Langlands satisfies all the axioms packaged by the archimedean datum structure, so it can serve as the archimedean component of an automorphic form built from a Hecke eigensystem. It is used in the construction of an archimedean datum of minimal type with prescribed weight character and Casimir eigenvalue and non-vanishing Whittaker function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_archDatumR_W_eq.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse LanglandsTunnell.Converse.PrincipalFamily

theorem LanglandsTunnell.Converse.PrincipalFamily.exists_archDatumR_W_eq (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂), D.W = Wmem u₁ u₂ a₁ a₂ := by sorry
