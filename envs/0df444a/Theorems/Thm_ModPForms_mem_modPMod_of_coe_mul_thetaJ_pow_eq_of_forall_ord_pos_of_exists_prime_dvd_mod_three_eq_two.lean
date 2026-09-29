-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
-- name    : ModPForms.mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/516d5345-b485-54f3-b149-f38aaf977104
-- title:
--   Descent from weight 2m+2 to 2m for mod-3 forms
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$ admitting a prime divisor $q$ with $q \equiv 2 \pmod 3$, let $F$ be a field of characteristic $3$, let $m$ be a natural number, and let $\varphi \in F[[q]]$. Assume $\varphi$ lies in `modPMod N' (2*(m:ℤ)+2) F`, the $F$-span inside $F[[q]]$ of the series $\sum_n \bar a_n q^n$ arising from a modular form $f$ of weight $2m+2$ on $\Gamma_0(N')$ whose $q$-expansion coefficients are the integers $a_n$, reduced into $F$. Let $G$ be an element of [`ModularCurve.modularFunctionFieldC F N'`](def/ModularCurve_JqCoeff.html#L61), the intermediate field of `LaurentSeries F` generated over $F$ by the $q$-expansions `jqModC F` of $j$ and `jqNModC F N'` of $j(q^{N'})$, and assume that, as Laurent series, $G \cdot \theta j^{\,m} = \varphi$, where $\theta j = q\,\mathrm{d}/\mathrm{d}q$ applied to `jqModC F`. Assume finally that for every place $x$ of this function field over $F$ (a proper valuation subring containing $F$ whose ring is a principal ideal ring) with $\operatorname{ord}_x(j) > 0$, where $j$ denotes [`ModularCurve.jGeomGen F N'`](def/ModularCurve_CharLSpecialFibreLevelNDictionary.html#L82) and $\operatorname{ord}_x$ is minus the logarithm of the associated adic valuation, one has $0 \le 6\operatorname{ord}_x(G) + 7m\operatorname{ord}_x(j)$. Then $\varphi$ lies in `modPMod N' (2*(m:ℤ)) F`.
--
--   This is the exactness statement, in the currency of $q$-expansions, of Edixhoven's sequence relating mod-$3$ forms of weight $2m$, weight $2m+2$ and their values at the supersingular points (the places over $j = 0$ in characteristic $3$): a weight-$(2m+2)$ reduction whose associated weight-$2m$ function-field datum has no pole over $j=0$ is itself a weight-$2m$ reduction, i.e. the Hasse invariant times such a reduction. It feeds the weight-six descent for mod-$3$ forms, being cited by [`ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed) and by [`ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F) (G : ↥(ModularCurve.modularFunctionFieldC F N'))
    (hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ)
    (hvan : ∀ x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'),
      0 < x.ord (ModularCurve.jGeomGen F N') →
        0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N')) :
    φ ∈ modPMod N' (2 * (m : ℤ)) F := by sorry
