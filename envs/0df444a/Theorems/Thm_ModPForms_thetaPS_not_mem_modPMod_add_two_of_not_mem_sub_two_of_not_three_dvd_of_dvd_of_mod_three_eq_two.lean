-- Prove2me | Theorems.Thm_ModPForms_thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two
-- name    : ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/9952257f-f26a-5021-802c-ab759a5d166c
-- title:
--   Theta raises the mod-3 filtration past weight k+2
-- statement:
--   Fix a natural number $N'$, assumed nonzero, with $3 \nmid N'$, and suppose $N'$ has a divisor $d$ with $d \equiv 2 \pmod 3$. Let $F$ be a field of characteristic $3$, and let $k$ be an integer with $k \ge 4$ and $3 \nmid k$. For an integer weight $j$ write $M_j$ for `modPMod N' j F`, the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \overline{a_n} q^n$ for which there are a modular form $f$ of weight $j$ on $\Gamma_0(N')$ and integers $a_n$ with the $n$-th coefficient of the $q$-expansion of $f$ (taken with width $1$) equal to $a_n$ for every $n$, the bar denoting the image of an integer in $F$. Let $\varphi \in F[[q]]$ satisfy $\varphi \in M_k$ and $\varphi \notin M_{k-2}$. The conclusion is that `thetaPS` $\varphi$, the power series whose $n$-th coefficient is $n$ times the $n$-th coefficient of $\varphi$, does not lie in $M_{k+2}$.
--
--   This is the case $p = 3$ of the statement that, on forms of exact filtration $k$ with $p \nmid k$, the operator $\theta = q\,d/dq$ raises the filtration by $p+1$ rather than by $2$; the hypotheses that $3 \nmid N'$, that $N'$ have a divisor congruent to $2$ modulo $3$, and that $3 \nmid k$ are all part of the assertion. It is used in the proof of [`ModPForms.mem_modPMod_two_of_mem_modPMod_four_of_forall_coeff_three_mul_eq_zero_of_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.mem_modPMod_two_of_mem_modPMod_four_of_forall_coeff_three_mul_eq_zero_of_exists_prime_dvd_mod_three_eq_two), which descends from weight $4$ to weight $2$ for mod-$3$ forms whose coefficients in degrees divisible by $3$ vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (d : ℕ) (hd : d ∣ N') (hd3 : d % 3 = 2)
    (F : Type) [Field F] [CharP F 3] (k : ℤ) (hk : 4 ≤ k) (h3k : ¬ (3 : ℤ) ∣ k)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) (hlow : φ ∉ modPMod N' (k - 2) F) :
    thetaPS φ ∉ modPMod N' (k + 2) F := by sorry
