-- Prove2me | Theorems.Thm_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
-- name    : ModPForms.exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/505051a7-d8f4-5fa4-94a9-0c027dfb031d
-- title:
--   Eichler–Shimura modulo 3 in weight at most 4
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$ which admits a prime divisor $q$ with $q \equiv 2 \pmod 3$, let $S_0$ be a finite set of natural numbers containing $3$, let $F$ be a field of characteristic $3$, let $a \le 2$, and let $\lambda : \mathbb{N} \to F$. Write $\rho$ for the restriction to $\Gamma_0(N') \le \mathrm{SL}_2(\mathbb{Z})$ of the representation [`HeckeEis.binaryFormRepSL F a`](def/HeckeEis_BinaryFormRep.html#L61) on the space of degree-$a$ homogeneous polynomials in $X_0, X_1$ over $F$, given by the substitution $X_j \mapsto \sum_i M_{ij} X_i$. Assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for $\rho$, the operators $\ell \mapsto$ `binaryFormAlphaAdj F a ℓ` (substitution by $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1) \mapsto P(\ell X_0, X_1)$), the set $S_0$ and $\lambda$: there is a nonzero class $x$ in the quotient `coeffH1` of the cocycles of $\rho$ by the coboundaries such that for every prime $\ell$ with $\ell \nmid N'$ and $\ell \notin S_0$ some $F$-linear endomorphism $T$ of `coeffH1` is induced by the cochain-level operator `coeffHeckeFun N' ℓ ρ (binaryFormAlphaAdj F a ℓ)` (each cocycle is carried to a cocycle representing $T$ of its class) and satisfies $T x = \lambda(\ell) \, x$. The conclusion is that there are a natural number $j$, a power series $\psi$ over $F$ and a function $\mu : \mathbb{N} \to F$ such that $\psi$ lies in the $F$-span of the coefficientwise reductions of the integral $q$-expansions of modular forms of weight $(a : \mathbb{Z}) + 2$ on $\Gamma_0(N')$, $\psi \neq 0$, and for every prime $\ell$ with $\ell \nmid N'$ and $\ell \notin S_0$ one has $T_\ell \psi = \mu(\ell) \, \psi$ for the formal Hecke operator whose $n$-th coefficient is $c_{n\ell}(\psi) + \ell^{(a+2)-1} c_{n/\ell}(\psi)$ when $\ell \mid n$ and $c_{n\ell}(\psi)$ otherwise, together with $\mu(\ell) = \ell^{j} \lambda(\ell)$.
--
--   This is the characteristic-$3$ case of the passage from a Hecke eigensystem in the first cohomology of $\Gamma_0(N')$ with binary-form coefficients to a mod-$3$ modular form of weight $a+2 \le 4$ with the same eigenvalues up to a power of $\ell$, the hypothesis that $N'$ have a prime divisor $q \equiv 2 \pmod 3$ taking the place of the condition $p \ge 5$ used for larger primes. It feeds the weight-at-most-four statement [`ModPForms.exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two) in the mod-$3$ part of the level- and weight-optimisation argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModPForms.exists_mem_modPMod_isModPEigen_of_isEigensystemH1_binaryFormRepSL_three_of_exists_prime_dvd_mod_three_eq_two
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : 3 ∈ S₀) (F : Type) [Field F] [CharP F 3]
    (a : ℕ) (ha : a ≤ 2) (lam : ℕ → F)
    (hocc : HeckeEis.IsEigensystemH1 N'
      ((HeckeEis.binaryFormRepSL F a).comp (CongruenceSubgroup.Gamma0 N').subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F a ℓ) S₀ lam) :
    ∃ (j : ℕ) (ψ : PowerSeries F) (mu : ℕ → F),
      ψ ∈ ModPForms.modPMod N' ((a : ℤ) + 2) F ∧ ModPForms.IsModPEigen N' S₀ ((a : ℤ) + 2) ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : F) ^ j * lam ℓ := by sorry
