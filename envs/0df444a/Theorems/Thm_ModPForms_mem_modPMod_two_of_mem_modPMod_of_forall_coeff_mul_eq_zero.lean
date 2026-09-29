-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero
-- name    : ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8eb579ff-22b3-5cd6-b668-a028b3a573d3
-- title:
--   Filtration drop in weight p+1 for forms killed by Uₚ
-- statement:
--   Fix a prime $p$ with $p \ge 5$, a natural number $N' \neq 0$ with $p \nmid N'$, and a field $F$ of characteristic $p$. For an integer $k$ let $\mathrm{modPMod}\ N'\ k\ F \subseteq F[[q]]$ denote the $F$-submodule spanned by those power series of the form $\sum_n \overline{a_n}\, q^n$ (i.e. `PowerSeries.mk (fun n => (a n : F))`) for which there is an integer sequence $a : \mathbb{N} \to \mathbb{Z}$ and a modular form $f$ of weight $k$ on $\Gamma_0(N')$ whose $q$-expansion coefficients (of width $1$) satisfy $\mathrm{qCoeff}\ f\ n = a_n$ in $\mathbb{C}$ for every $n$; thus $\mathrm{modPMod}\ N'\ k\ F$ is the span of the reductions to $F$ of the integral $q$-expansions of weight-$k$ forms on $\Gamma_0(N')$. Let $\varphi \in F[[q]]$ lie in $\mathrm{modPMod}\ N'\ (p+1)\ F$ and suppose that the coefficient of $q^{pn}$ in $\varphi$ vanishes for every natural number $n$. The conclusion is that $\varphi$ lies in $\mathrm{modPMod}\ N'\ 2\ F$, that is, $\varphi$ is in the span of reductions of integral $q$-expansions of weight-$2$ forms on $\Gamma_0(N')$.
--
--   This is the filtration-drop step in the weight part of Serre's conjecture: a mod $p$ form of weight $p+1$ annihilated by $U_p$ (equivalently, in characteristic $p$, by $T_p$) already has filtration at most $2$. It is used in the construction of a weight-$2$ system of Hecke eigenvalues from a weight-$(p+1)$ one with $T_p \mapsto 0$, via [`CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd`](thm.html#CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModPForms

theorem ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (F : Type) [Field F] [CharP F p] (φ : PowerSeries F) (hφ : φ ∈ modPMod N' ((p : ℤ) + 1) F)
    (hT : ∀ n : ℕ, PowerSeries.coeff (p * n) φ = 0) :
    φ ∈ modPMod N' 2 F := by sorry
