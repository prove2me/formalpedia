-- Prove2me | Theorems.Thm_ModPForms_res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
-- name    : ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/3d4f2080-2068-5a8b-b185-572c302fcf5e
-- title:
--   Non-vanishing at supersingular places of a weight-four series mod 3
-- statement:
--   Let $N'$ be a nonzero natural number not divisible by $3$, let $d$ be a divisor of $N'$ with $d \equiv 2 \pmod 3$, and let $F$ be an algebraically closed field of characteristic $3$. Let $B \in F[[q]]$ be the power series whose $n$-th coefficient is the image in $F$ of the integer $\sigma_1(n) - \sigma_1(n/d)$, the second term being present only when $d \mid n$. The assertion is: if $B$ lies in `modPMod N' 4 F`, the $F$-span inside $F[[q]]$ of those series $\mathrm{mk}(n \mapsto \overline{a_n})$ for which some modular form $f$ of weight $4$ on $\Gamma_0(N')$ has $q$-expansion coefficients $\mathrm{qCoeff}(f)(n) = a_n$ with $a_n \in \mathbb{Z}$, then for every $x$ in [`ModularCurve.ssPlaces3 F N'`](def/ModularCurve_SSCarrier3.html#L11) — that is, every place $x$ of the intermediate field $\mathrm{modularFunctionFieldC}\,F\,N' = F(\,j_q, j_{q,N}\,) \subseteq F((q))$, given by a valuation subring containing $F$, proper, and a principal ideal ring, such that $\mathrm{ord}_x(\mathrm{jGeomGen}\,F\,N') > 0$ — one has $\mathrm{res}_1(B)(x) \neq 0$ in the residue field of $x$. Here $\mathrm{res}_1(B)(x)$ is: $0$ unless there is $G$ in that function field with $G \cdot \mathrm{thetaJ}\,F = B$ as Laurent series, in which case, for a chosen such $G$ and a chosen uniformiser $\pi_x$ at $x$, it is the residue of $G \cdot \pi_x^{a}$ with $a = \max(0, \lfloor 7\,\mathrm{ord}_x(\mathrm{jGeomGen}\,F\,N')/6 \rfloor + 1)$, when that element is in the valuation subring, and $0$ otherwise.
--
--   This is the non-vanishing, at every place above the supersingular $j$-invariant in characteristic $3$, of the mod $3$ weight-four series built from the Eisenstein combination $\sigma_1(n) - \sigma_1(n/d)$ attached to a divisor $d \equiv 2 \pmod 3$ of the level; the shape $B \in \mathrm{modPMod}\,N'\,4\,F$ is taken as a hypothesis rather than proved. It feeds the multiplication-by-$B$ step in [`ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed), which moves between weights in the mod $3$ filtration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed.lean

import Definitions.Def_ModularCurve_SSCarrier3
import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (d : ℕ) (hd : d ∣ N') (hd3 : d % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    B ∈ modPMod N' 4 F → ∀ x : ModularCurve.ssPlaces3 F N', ModularCurve.SSCarrier3.res 1 B x ≠ 0 := by sorry
