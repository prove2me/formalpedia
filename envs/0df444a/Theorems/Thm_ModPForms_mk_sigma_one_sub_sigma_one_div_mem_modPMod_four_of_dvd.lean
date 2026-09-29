-- Prove2me | Theorems.Thm_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
-- name    : ModPForms.mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/4194bb9d-f524-5827-94ca-a5636bc11ed0
-- title:
--   A weight-four form mod 3 with coefficients σ₁(n)-σ₁(n/d)
-- statement:
--   Let $N'$ be a natural number with $N'\neq 0$, let $d$ be a natural number dividing $N'$, and let $F$ be a field of characteristic $3$. Consider the power series $B\in F[[q]]$ whose $n$-th coefficient is the image in $F$ of the integer $\sigma_1(n)-\bigl[d\mid n\bigr]\,\sigma_1(n/d)$, that is, of $\sigma_1(n)$ minus $\sigma_1(n/d)$ when $d\mid n$ and of $\sigma_1(n)$ otherwise, $\sigma_1$ being the divisor-sum arithmetic function. The assertion is that $B$ lies in `modPMod N' 4 F`, the $F$-submodule of $F[[q]]$ spanned by those power series $\varphi$ for which there exist a modular form $f$ of weight $4$ for $\Gamma_0(N')$ and a function $a:\mathbb{N}\to\mathbb{Z}$ such that the $n$-th coefficient of the period-$1$ $q$-expansion of $f$ equals $a(n)$ for every $n$ and $\varphi=\sum_n \overline{a(n)}\,q^n$ with $\overline{\,\cdot\,}$ the reduction $\mathbb{Z}\to F$. In other words, $B$ is a form of weight $4$ and level $\Gamma_0(N')$ modulo $3$ in the sense of reductions of integral $q$-expansions; the proof in fact exhibits $B$ as one such reduction rather than merely as a combination of them.
--
--   This is the standard construction, in the style of Serre and Swinnerton-Dyer, of an explicit nonzero weight-four form modulo $3$ of level $\Gamma_0(N')$: the reduction of $\bigl(E_4(\tau)-E_4(d\tau)\bigr)/240$, whose coefficients are $\sigma_3(n)-\sigma_3(n/d)\equiv\sigma_1(n)-\sigma_1(n/d)\pmod 3$. It supplies the source form in the mod-$3$ level- and weight-raising arguments, and is used by [`ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed) and [`ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (F : Type) [Field F] [CharP F 3] :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    B ∈ modPMod N' 4 F := by sorry
