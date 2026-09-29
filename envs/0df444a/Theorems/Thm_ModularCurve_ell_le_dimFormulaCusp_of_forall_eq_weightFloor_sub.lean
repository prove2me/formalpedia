-- Prove2me | Theorems.Thm_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
-- name    : ModularCurve.ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/50ef4f56-8740-5488-a5b1-71628605d5b3
-- title:
--   Riemann–Roch bound for the cuspidal weight-2m floor divisor
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ be an integer with $p\nmid N$, let $K$ be an algebraically closed field of characteristic $p$, and let $m\ge 1$. Write $F=$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by $\bar\jmath=$ `jqModC K` and by its $N$-th transform `jqNModC K N`, and let $j\in F$ denote the element `jGeomGen K N`, i.e. $\bar\jmath$ viewed in $F$. Let $E$ be a divisor of $F/K$, that is a finitely supported $\mathbb{Z}$-valued function on the places of $F/K$ (valuation subrings containing $K$, proper, with principal ideals), and assume that at every place $w$ one has $$E(w)=\Big[\text{$0<\mathrm{ord}_w(j)$}\Big]\big\lfloor \tfrac{2m\,\mathrm{ord}_w(j)}{3}\big\rfloor+\Big[\text{$0<\mathrm{ord}_w(j-1728)$}\Big]\big\lfloor\tfrac{m\,\mathrm{ord}_w(j-1728)}{2}\big\rfloor+\Big[\mathrm{ord}_w(j)<0\Big]\big(m\,\mathrm{ord}_w(j)-1\big),$$ the weight-$2m$ floor divisor `weightFloor K N m` minus the reduced divisor supported on the poles of $j$ (the divisions are integer divisions, with nonnegative numerators in the branches where they occur). Then the $K$-dimension $\ell(E)$ of the Riemann–Roch space $L(E)$ satisfies $$\ell(E)\le(2m-1)\big(g_N-1\big)+\lfloor m/2\rfloor\,\nu_2(N)+\lfloor 2m/3\rfloor\,\nu_3(N)+(m-1)\,\nu_\infty(N)+[m=1],$$ where $\nu_2(N)=\#\{x\in\mathbb{Z}/N:x^2+1=0\}$, $\nu_3(N)=\#\{x\in\mathbb{Z}/N:x^2+x+1=0\}$, $\nu_\infty(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d))$, and $g_N=1+\psi(N)/12-\nu_2(N)/4-\nu_3(N)/3-\nu_\infty(N)/2$ with $\psi(N)=\sum_{d\mid N,\ d\text{ squarefree}}N/d$.
--
--   The right-hand side is the classical complex dimension formula for the space $S_{2m}(\Gamma_0(N))$ of cusp forms, so the statement bounds the dimension of the Riemann–Roch space attached to the cuspidal weight-$2m$ floor divisor on the modular curve of level $N$ in characteristic $p\ge 5$ by the characteristic-zero cusp form dimension. It is used in the comparison of mod $p$ modular forms with their characteristic-zero counterparts, notably in the lemmas [`ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn`](thm.html#ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn) and [`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (m : ℕ) (hm : 1 ≤ m)
    (E : Divisor K ↥(modularFunctionFieldC K N))
    (hE : ∀ w : Place K ↥(modularFunctionFieldC K N),
      E w = ModularCurve.weightFloor K N m w - (if w.ord (jGeomGen K N) < 0 then 1 else 0)) :
    (ell E : ℚ) ≤ (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)
        + (if m = 1 then 1 else 0) := by sorry
