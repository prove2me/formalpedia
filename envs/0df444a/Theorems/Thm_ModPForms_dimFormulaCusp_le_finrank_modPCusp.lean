-- Prove2me | Theorems.Thm_ModPForms_dimFormulaCusp_le_finrank_modPCusp
-- name    : ModPForms.dimFormulaCusp_le_finrank_modPCusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/11cccde6-04fe-509f-af6c-8a396421db85
-- title:
--   Dimension lower bound for mod-F cusp forms of weight 2m
-- statement:
--   Let $N\ge 1$ be a natural number, let $m$ be a natural number with $1\le m$, and let $F$ be a field. Write $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}} N/d$, $\nu_2(N)=\#\{x\in\mathbb{Z}/N:x^2+1=0\}$, $\nu_3(N)=\#\{x\in\mathbb{Z}/N:x^2+x+1=0\}$, $\nu_\infty(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d))$, and let $g(N)=1+\psi(N)/12-\nu_2(N)/4-\nu_3(N)/3-\nu_\infty(N)/2$ be the genus expression [`ModularCurve.genusFormula`](def/ModularCurve_GenusNumerics.html#L20). The assertion is the inequality of rational numbers $$(2m-1)\bigl(g(N)-1\bigr)+\lfloor m/2\rfloor\,\nu_2(N)+\lfloor 2m/3\rfloor\,\nu_3(N)+(m-1)\,\nu_\infty(N)+[m=1]\ \le\ \dim_F \widetilde S,$$ where the two quotients $m/2$ and $2m/3$ are truncated natural-number divisions, $[m=1]$ is $1$ if $m=1$ and $0$ otherwise, and $\widetilde S=$ [`ModPForms.modPCusp N (2*m) F`](def/CuspForm_ModPForms.html#L7) is the $F$-submodule of $F[[q]]$ spanned by all power series $\sum_n \overline{a_n}q^n$ with $a:\mathbb{N}\to\mathbb{Z}$ such that some cusp form $f$ of weight $2m$ on $\Gamma_0(N)$ has $q$-expansion coefficients $\mathrm{qCoeff}(f,n)=a_n$ for all $n$, the coefficients being reduced into $F$ along $\mathbb{Z}\to F$.
--
--   The left-hand side is the classical dimension formula for the space $S_{2m}(\Gamma_0(N))$ of complex cusp forms, the summand $[m=1]$ making a single expression valid for all $m\ge 1$; the statement transfers that formula into a lower bound for the dimension over an arbitrary field $F$ of the space of reductions of integral $q$-expansions. It is used by [`ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn`](thm.html#ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn) and by [`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_dimFormulaCusp_le_finrank_modPCusp.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.dimFormulaCusp_le_finrank_modPCusp (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) (F : Type) [Field F] :
    ((2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)
        + (if m = 1 then 1 else 0))
      ≤ (Module.finrank F ↥(ModPForms.modPCusp N (2 * (m : ℤ)) F) : ℚ) := by sorry
