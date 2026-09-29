-- Prove2me | Theorems.Thm_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
-- name    : ModPForms.finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/b35b11fe-8ec1-55be-8d9c-16efd1facdca
-- title:
--   Dimension bound for mod-p reductions of weight-two forms
-- statement:
--   Let $N$ be a nonzero natural number and let $F$ be a field (no assumption is made on its characteristic). Consider the $F$-submodule [`ModPForms.modPMod N 2 F`](def/CuspForm_ModPForms.html#L12) of $F[[q]]$ spanned by those power series $\varphi$ for which there exist a modular form $f$ of weight $2$ for $\Gamma_0(N)$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ such that the $n$-th coefficient of the $q$-expansion of $f$ (with width $1$) equals $a_n$ for every $n$, and $\varphi = \sum_n (a_n \bmod F)\, q^n$ is the coefficientwise image of $a$ in $F$. The assertion is that the $F$-dimension of this span, viewed as a rational number, is at most
--   $$\Big(1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{c(N)}{2}\Big) + c(N) - 1,$$
--   where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, where $\nu_2(N)$ and $\nu_3(N)$ are the numbers of $x \in \mathbb{Z}/N$ with $x^2+1 = 0$ and with $x^2+x+1 = 0$ respectively, and where $c(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$ is the cusp count.
--
--   The bracketed expression is the genus formula for $X_0(N)$ and $c(N)$ the number of its cusps, so the bound is the classical estimate $\dim M_2(\Gamma_0(N)) \le g(N) + c(N) - 1$ transported to the span of the mod-$F$ reductions of the integral weight-two forms. It is used in the nonvanishing statement [`ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed), where a dimension count over an algebraically closed field of characteristic $p$ forces a residual form to be nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one (N : ℕ) [NeZero N]
    (F : Type) [Field F] :
    (Module.finrank F ↥(modPMod N 2 F) : ℚ) ≤
      ModularCurve.genusFormula N + (ModularCurve.cuspCount N : ℚ) - 1 := by sorry
