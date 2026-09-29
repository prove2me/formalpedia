-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_oddComb_ne_zero
-- name    : LanglandsTunnell.Converse.PrincipalFamily.exists_oddComb_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/7f419f0e-3ed8-544b-bc77-0fcc4eb44da3
-- title:
--   Non-vanishing of the odd weight-one Whittaker combination
-- statement:
--   For every pair of complex numbers $u_1,u_2$ there exists an invertible real $2\times 2$ matrix $g$ (an element of $\mathrm{GL}_2(\mathbb{R})$, used through its underlying matrix) such that
--   $$\mathrm{Wmem}(u_1,u_2,1,0)(g) + i\,\operatorname{sgn}(\det g)\,\mathrm{Wmem}(u_1,u_2,0,1)(g) \neq 0 ,$$
--   where $\operatorname{sgn}(\det g)$ is the sign of the determinant, viewed as a real number and then as a complex number. Here, for $a_1,a_2\in\mathbb{Z}/2$, `Wmem` is the explicit archimedean principal-series Whittaker integral
--   $$\mathrm{Wmem}(u_1,u_2,a_1,a_2)(g)=|\det g|\cdot \mathrm{quasiChar}(u_1,a_1)(\det g)\cdot\int_{\mathbb{R}} \mathrm{innerW}(a_1,a_2,g)(t)\,\mathrm{quasiChar}(u_1-u_2,a_1+a_2)(t)\,dt,$$
--   with $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ for $a=0$ and $|y|^{u}\operatorname{sgn}(y)$ for $a\neq 0$, and
--   $$\mathrm{innerW}(a_1,a_2,h)(t)=\int_{\mathbb{R}} \mathrm{phiStd}_{a_1}\!\big(-t(h_{00}+x\,h_{10})\big)\,\mathrm{phiStd}_{a_2}\!\big(-t(h_{01}+x\,h_{11})\big)\,\mathrm{psi}(-x)\,dx,$$
--   for the fixed real test functions `phiStd` indexed by $\mathbb{Z}/2$ and the fixed additive character `psi` of $\mathbb{R}$. Both integrals are Bochner integrals, hence are $0$ whenever the integrand fails to be integrable; in particular the assertion is that the displayed combination is non-zero at some $g$, so that the two quantities do not both degenerate.
--
--   This is the non-vanishing input for the weight-one vector in the archimedean Whittaker model: the combination $W_{1,0}+i\operatorname{sgn}(\det)\,W_{0,1}$ is the coordinate of the relevant $K$-type of the real principal series, and the statement says it is not identically zero on $\mathrm{GL}_2(\mathbb{R})$. It is used in the construction of a non-zero archimedean datum with prescribed weight character, minimal type and Casimir eigenvalue in the converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_oddComb_ne_zero.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse.PrincipalFamily

theorem LanglandsTunnell.Converse.PrincipalFamily.exists_oddComb_ne_zero (u₁ u₂ : ℂ) :
    ∃ g : GL (Fin 2) ℝ,
      Wmem u₁ u₂ 1 0 (g : Matrix (Fin 2) (Fin 2) ℝ)
          + Complex.I * (((SignType.sign (g : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
            * Wmem u₁ u₂ 0 1 (g : Matrix (Fin 2) (Fin 2) ℝ)) ≠ 0 := by sorry
