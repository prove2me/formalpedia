-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
-- name    : ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6f407126-4207-5ebb-9383-c3f7486d43e9
-- title:
--   Weight detection by B_d over 𝔽̄₃
-- statement:
--   Let $N'$ be a nonzero natural number not divisible by $3$, let $d$ be a divisor of $N'$ with $d \equiv 2 \pmod 3$, and let $F$ be an algebraically closed field of characteristic $3$. For an integer weight $k$ write $\mathrm{modPMod}\,N'\,k\,F$ for the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\mathrm{PowerSeries.mk}\,(n \mapsto (a(n) : F))$ for which $a : \mathbb{N} \to \mathbb{Z}$ is a sequence of integers that are the Fourier coefficients of some modular form $f$ of weight $k$ on $\Gamma_0(N')$, in the sense that the $n$-th coefficient of the $q$-expansion of $f$ (with respect to width $1$) equals $(a(n) : \mathbb{C})$ for all $n$. Let $B \in F[[q]]$ be the power series whose $n$-th coefficient is the image in $F$ of $\sigma_1(n) - \sigma_1(n/d)$, the subtracted term being present only when $d \mid n$. Then for every integer $k$ with $4 \le k$ and every $\varphi \in \mathrm{modPMod}\,N'\,k\,F$: if $B\varphi \in \mathrm{modPMod}\,N'\,(k+2)\,F$, then already $\varphi \in \mathrm{modPMod}\,N'\,(k-2)\,F$.
--
--   The series $B$ is the reduction modulo $3$ of the weight-$4$ form $(E_4(z) - E_4(dz))/240$ on $\Gamma_0(d)$, and the assertion is that multiplication by $B$ detects a drop of weight: it is injective on mod-$3$ forms of weight $k$ modulo those of weight $k-2$, the passage between consecutive even weights being multiplication by the Hasse invariant. It is the single case, for an algebraically closed field of constants, of the weight-ladder theorem that is needed for the jump of the $\theta$-operator at $3$, and it is used in the proof that the relevant $\theta$-series does not lie in weight $k+2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed (N' : ℕ) [NeZero N']
    (hpN' : ¬ 3 ∣ N') (d : ℕ) (hd : d ∣ N') (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (k : ℤ) (hk : 4 ≤ k) :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    (∀ φ ∈ modPMod N' k F, B * φ ∈ modPMod N' (k + 2) F → φ ∈ modPMod N' (k - 2) F) := by sorry
