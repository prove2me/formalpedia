-- Prove2me | Theorems.Thm_ModPForms_heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two
-- name    : ModPForms.heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8fd78fbd-f1a4-509e-9389-35ed0f7f84cc
-- title:
--   U₃ sends mod-3 cusp forms of level 3N to weight 4
-- statement:
--   Let $N$ be a natural number with $3 \nmid N$ and suppose there is a prime $q$ with $q \mid N$ and $q \equiv 2 \pmod 3$. Let $F$ be a field of characteristic $3$. For a level $M$ and weight $k$, [`ModPForms.modPCusp M k F`](def/CuspForm_ModPForms.html#L7) denotes the $F$-submodule of $F\llbracket X\rrbracket$ spanned by all power series of the form $\mathrm{mk}\,(n \mapsto (a_n \bmod 3))$ where $a : \mathbb{N} \to \mathbb{Z}$ and there exists a cusp form $f$ of weight $k$ on $\Gamma_0(M)$ whose $q$-expansion coefficients (the coefficients of `qExpansion 1 f`) satisfy $\mathrm{qCoeff}(f)(n) = a_n$ in $\mathbb{C}$ for all $n$; that is, the span of the coefficientwise reductions mod $3$ of integrally expanded cusp forms. The assertion is that for every $\varphi \in F\llbracket X\rrbracket$ lying in [`ModPForms.modPCusp (N * 3) 2 F`](def/CuspForm_ModPForms.html#L7), the power series [`PowerSeries.heckeU 3 φ`](def/PowerSeries_FormalHeckeOperators.html#L11), whose $n$-th coefficient is the $(3n)$-th coefficient of $\varphi$, lies in [`ModPForms.modPCusp N 4 F`](def/CuspForm_ModPForms.html#L7).
--
--   This is the case $p = 3$ of the passage from weight $2$ and level $Np$ to weight $p+1$ and level $N$ for mod-$p$ cusp forms, the hypotheses $3 \nmid N$ and $q \equiv 2 \pmod 3$ for some prime $q \mid N$ replacing the use of $E_{p-1} \equiv 1 \pmod p$, which is unavailable at $p = 3$. It is used in the comparison of mod-$3$ cusp form spaces in [`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two.lean

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two
    (N : ℕ) (h3N : ¬ 3 ∣ N) (hq : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (F : Type) [Field F] [CharP F 3]
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp (N * 3) 2 F) :
    PowerSeries.heckeU 3 φ ∈ ModPForms.modPCusp N 4 F := by sorry
