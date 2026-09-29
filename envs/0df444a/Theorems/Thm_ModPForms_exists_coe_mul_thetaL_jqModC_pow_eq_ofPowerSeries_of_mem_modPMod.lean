-- Prove2me | Theorems.Thm_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
-- name    : ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/393d7fcd-eaf7-5a93-a520-6b259581b840
-- title:
--   Mod p forms lie in (θ̄ j)^m F(̄ j,̄ j_N)
-- statement:
--   Let $p$ be a prime, $N\ge 1$ an integer with $p\nmid N$, $F$ a field of characteristic $p$, $m$ a natural number and $\varphi$ a power series over $F$. Assume $\varphi$ lies in [`ModPForms.modPMod N (2*m) F`](def/CuspForm_ModPForms.html#L12), that is, in the $F$-linear span of those power series of the form $\sum_n \overline{a_n}\,q^n$ for which there exist a modular form $f$ of weight $2m$ on $\Gamma_0(N)$ and integers $a_n$ with $n$-th $q$-expansion coefficient of $f$ equal to $a_n$ for all $n$, the bar denoting the image of an integer in $F$. Write $\bar j = q^{-1}\cdot \overline{E_4^3\eta^{-24}} \in F((q))$ for `jqModC F`, the reduction of the $q$-expansion of the modular invariant, and $\theta = q\,\frac{d}{dq}$ for the operator `thetaL F`. The assertion is that there exists $G$ in the intermediate field of $F((q))$ generated over $F$ by $\bar j$ and by its substitution $q\mapsto q^N$, namely `modularFunctionFieldC F N`, such that $G\cdot(\theta\bar j)^m = \varphi$ as Laurent series over $F$.
--
--   This is the membership half of the bridge between Serre-style mod $p$ modular forms of even weight $2m$ on $\Gamma_0(N)$ and functions on the modular curve in characteristic $p$: dividing by $(\theta\bar j)^m$ carries reductions of integral forms into the level-$N$ modular function field $F(\bar j,\bar j_N)$, which has good reduction when $p\nmid N$. It is used in the constructions of mod $p$ forms and mod $p$ cusp forms from elements of `modPMod` and of the corresponding space of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (F : Type) [Field F] [CharP F p] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) F) :
    ∃ G : ↥(modularFunctionFieldC F N),
      (G : LaurentSeries F) * thetaL F (jqModC F) ^ m = HahnSeries.ofPowerSeries ℤ F φ := by sorry
