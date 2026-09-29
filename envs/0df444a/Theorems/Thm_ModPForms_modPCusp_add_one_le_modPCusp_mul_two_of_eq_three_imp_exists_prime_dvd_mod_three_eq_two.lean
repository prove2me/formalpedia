-- Prove2me | Theorems.Thm_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
-- name    : ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/ffad5b00-d5ca-5dd6-b523-1ff69398d62e
-- title:
--   Weight p+1 level N' embeds in weight 2 level N'p
-- statement:
--   Fix a natural number $p$ carrying the assumption that it is prime, with $p \neq 2$, and a natural number $N'$ with $p \nmid N'$ (which in particular forces $N' \neq 0$). Assume in addition that $3 < p$ or $3 < N'$, and that if $p = 3$ then $N'$ has a prime divisor $q$ with $q \equiv 2 \pmod 3$. Let $F$ be a field of characteristic $p$. For a level $N$ and a weight $k \in \mathbb{Z}$, write $\mathrm{modPCusp}\,N\,k\,F$ for the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \bar{a}_n q^n$, where $a : \mathbb{N} \to \mathbb{Z}$ is an integer sequence and there is a cusp form $f$ of weight $k$ on $\Gamma_0(N)$ whose $q$-expansion coefficients at the cusp at infinity satisfy $\mathrm{qCoeff}\,f\,n = a_n$ for all $n$, the bar denoting reduction into $F$. The assertion is the inclusion of submodules $\mathrm{modPCusp}\,N'\,(p+1)\,F \le \mathrm{modPCusp}\,(N' p)\,2\,F$.
--
--   This is the weight-for-level trade modulo $p$ in a purely spanwise form: an inclusion of two subspaces of $F[[q]]$, with no map, no Hecke equivariance and no statement about eigensystems. It is what carries a mod-$p$ system of Hecke eigenvalues occurring in weight $p+1$ and level $N'$ down to weight $2$ and level $N'p$, and is used in that form by the theta-cycle statement about ring homomorphisms on the cuspidal Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N' : ℕ) (hpN' : ¬ p ∣ N') (hside : 3 < p ∨ 3 < N')
    (hq3 : p = 3 → ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F p] :
    ModPForms.modPCusp N' ((p : ℤ) + 1) F ≤ ModPForms.modPCusp (N' * p) 2 F := by sorry
