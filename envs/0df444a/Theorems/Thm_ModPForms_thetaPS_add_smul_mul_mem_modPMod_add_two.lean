-- Prove2me | Theorems.Thm_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two
-- name    : ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/b055f432-706c-50d6-a8ba-0fcca6926511
-- title:
--   Characteristic 3: θ raises weight by two, twisted by B_d
-- statement:
--   Fix a positive integer $N'$ and a field $F$ of characteristic $3$, and for an integer $k$ write $M_k(N';F)$ for the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \bar a_n q^n$ arising from a modular form $f$ of weight $k$ on $\Gamma_0(N')$ together with a sequence of integers $(a_n)$ such that the $n$-th coefficient of the $q$-expansion of $f$ (at width $1$) equals $a_n$ for every $n$, the image of $a_n$ in $F$ being $\bar a_n$; this is the project notion [`ModPForms.modPMod`](def/CuspForm_ModPForms.html#L12). Let $\theta$ be the operator on $F[[q]]$ sending $\varphi$ to $\sum_n n\,c_n q^n$ when $\varphi=\sum_n c_n q^n$, and let $B_d \in F[[q]]$ be the power series whose $n$-th coefficient is the image in $F$ of the integer $\sigma_1(n) - \sigma_1(n/d)$, the second term being present only when $d \mid n$, where $\sigma_1$ is the sum-of-divisors function. The assertion is: for every divisor $d$ of $N'$ with $d \equiv 2 \pmod 3$, every integer $k$ and every $\varphi \in M_k(N';F)$, one has $\theta\varphi + k\,B_d\,\varphi \in M_{k+2}(N';F)$, where $k$ acts through its image in $F$.
--
--   This is the characteristic-$3$ substitute for Serre's derivation formula $12\,\theta f = k\,P f + (\text{a form of weight } k+2)$, in which the factor $12$ vanishes: the quasi-modular Eisenstein series $P$ is replaced by the weight-two series $B_d$ attached to a divisor $d \equiv 2 \pmod 3$ of the level. It is used in the companion result [`ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed), where the same hypotheses on $d$ yield a failure of $\theta$ to raise the weight by two in the absence of the correction term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] (k : ℤ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) :
    ModPForms.thetaPS φ + (k : F) •
      ((PowerSeries.mk fun n : ℕ =>
          ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
            (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)) * φ) ∈
      ModPForms.modPMod N' (k + 2) F := by sorry
