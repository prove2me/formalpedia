-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero
-- name    : LanglandsTunnell.Converse.PrincipalFamily.exists_Wmem_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/c8b78abf-0561-57b8-8605-b882e655524b
-- title:
--   Non-vanishing of the real principal-series Whittaker function
-- statement:
--   Let $u_1,u_2\in\mathbb{C}$ and let $a_1,a_2\in\mathbb{Z}/2$ be arbitrary; no further hypotheses are imposed. The assertion is that there exists an element $g$ of $\mathrm{GL}_2(\mathbb{R})$ whose underlying real $2\times 2$ matrix satisfies $\mathrm{Wmem}\,u_1\,u_2\,a_1\,a_2\,(g)\neq 0$. Here `Wmem` is the function
--   $$\mathrm{Wmem}(g)=|\det g|\cdot \mathrm{quasiChar}\,u_1\,a_1(\det g)\cdot\int_{\mathbb{R}}\mathrm{innerW}\,a_1\,a_2\,g\,(t)\cdot \mathrm{quasiChar}\,(u_1-u_2)\,(a_1+a_2)(t)\,dt,$$
--   where for $y\in\mathbb{R}$ one sets $\mathrm{quasiChar}\,u\,a\,(y)=|y|^{u}$ if $a=0$ and $|y|^{u}\operatorname{sign}(y)$ otherwise, and where the inner function of a real matrix $h$ at $t\in\mathbb{R}$ is
--   $$\mathrm{innerW}\,a_1\,a_2\,h\,(t)=\int_{\mathbb{R}}\mathrm{phiStd}\,a_1\bigl(-t(h_{00}+x\,h_{10})\bigr)\,\mathrm{phiStd}\,a_2\bigl(-t(h_{01}+x\,h_{11})\bigr)\,\psi(-x)\,dx,$$
--   with `phiStd` the standard archimedean Schwartz functions indexed by $\mathbb{Z}/2$ and `psi` the fixed additive character of $\mathbb{R}$. Both integrals are Bochner integrals, hence are $0$ when the integrand fails to be integrable, so the conclusion in particular asserts the integrability needed for a non-zero value at the chosen $g$.
--
--   This is the non-vanishing input for the archimedean principal series in the converse-theorem half of the Langlands–Tunnell argument: the explicitly constructed Whittaker function attached to the parameters $(u_1,u_2,a_1,a_2)$ is not identically zero on $\mathrm{GL}_2(\mathbb{R})$. It is used by [`LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero) to produce an archimedean datum with prescribed weight character, minimal type and Casimir eigenvalue whose Whittaker function is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse.PrincipalFamily

theorem LanglandsTunnell.Converse.PrincipalFamily.exists_Wmem_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ g : GL (Fin 2) ℝ, Wmem u₁ u₂ a₁ a₂ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by sorry
