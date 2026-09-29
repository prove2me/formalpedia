-- Prove2me | Theorems.Thm_ModPForms_exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two
-- name    : ModPForms.exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/22829c5a-97aa-5f08-afd7-8de15a230367
-- title:
--   Mod-3 eigensystems of level prime to 3 occur in weight ≤ 4
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$ admitting a prime divisor $q$ with $q \equiv 2 \pmod 3$, let $S_0$ be a finite set of natural numbers containing $3$, let $F$ be a field of characteristic $3$ and let $k \ge 2$ be an integer. Write $\mathrm{modPMod}\,N'\,k\,F$ for the $F$-submodule of $F[[q]]$ spanned by the power series $\sum_n (a_n \bmod 3)\,q^n$ arising from weight-$k$ modular forms $f$ on $\Gamma_0(N')$ whose $q$-expansion coefficients $\mathrm{qCoeff}\,f\,n$ are all integers $a_n$, the reduction being taken through the ring map $\mathbb{Z} \to F$. For a prime $\ell$ and weight $k$ let $\mathrm{heckePS}$ be the formal operator sending $\varphi$ to the series with $n$-th coefficient $\varphi_{n\ell} + \ell^{k-1}\varphi_{n/\ell}$ (the second term present only when $\ell \mid n$). Assume $\varphi \in \mathrm{modPMod}\,N'\,k\,F$ is nonzero and $\lambda : \mathbb{N} \to F$ satisfies $\mathrm{heckePS}\,k\,\ell\,\varphi = \lambda(\ell)\cdot\varphi$ for every prime $\ell$ with $\ell \nmid N'$ and $\ell \notin S_0$. Then there exist an integer $k'$ with $2 \le k' \le 4$, a natural number $j$, a nonzero $\psi \in \mathrm{modPMod}\,N'\,k'\,F$ and $\mu : \mathbb{N} \to F$ with $\mathrm{heckePS}\,k'\,\ell\,\psi = \mu(\ell)\cdot\psi$ for all primes $\ell \nmid N'$ outside $S_0$, and $\mu(\ell) = \ell^{j}\lambda(\ell)$ for all such $\ell$.
--
--   This is the weight-reduction step at $p = 3$ for systems of Hecke eigenvalues of mod-$3$ $q$-expansions of level prime to $3$: every such eigensystem occurs, after a twist by a power of the cyclotomic character, in weight $2$, $3$ or $4$. It is stated purely at the level of eigenvalue systems (no normalisation of the first coefficient) and is used in the construction of a weight-$\le 4$ mod-$3$ eigenform matching the traces of Frobenius of an elliptic curve, via [`WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
ModPForms.exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N')
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : 3 ∈ S₀) (F : Type) [Field F] [CharP F 3]
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F) (lam : ℕ → F)
    (hφ : φ ∈ modPMod N' k F) (heig : IsModPEigen N' S₀ k φ lam) :
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ 4 ∧ ∃ (j : ℕ) (ψ : PowerSeries F) (mu : ℕ → F),
      ψ ∈ modPMod N' k' F ∧ IsModPEigen N' S₀ k' ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : F) ^ j * lam ℓ := by sorry
