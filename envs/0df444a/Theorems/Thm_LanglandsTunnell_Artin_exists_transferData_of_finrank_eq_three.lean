-- Prove2me | Theorems.Thm_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three
-- name    : LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e678bec5-0848-5769-a223-d13d548a8802
-- title:
--   Artin transfer data for cyclic cubic extensions
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, the Galois group $\mathrm{Gal}(L/K)$ commutative, and $[L:K]=3$. Let $\mathfrak f$ be an ideal of $\mathcal O_K$ which is an admissible modulus for $L/K$ in the sense of `IsAdmissibleModulus`: $\mathfrak f \neq 0$, and for every height-one prime $v$ of $\mathcal O_K$ whose selected prime of $\mathcal O_L$ above it has non-trivial inertia subgroup in $\mathrm{Gal}(L/K)$, the power $v^{4e(v\mid 2)+2e(v\mid 3)+1}$ divides $\mathfrak f$, where $e(v\mid \ell)$ denotes the ramification index of $v$ over the rational prime $\ell$. Write $I_K(\mathfrak f)$ for `coprimeToModulus K 𝔣`, the group of units of the fractional ideals of $K$ whose valuation vanishes at every prime dividing $\mathfrak f$, and `primeCarriers K 𝔣` for the subset of those elements given by a single height-one prime $v \nmid \mathfrak f$. Then there exist $\sigma \in \mathrm{Gal}(L/K)$, a commutative group $I$, and families indexed by the elements $p$ of $I_K(\mathfrak f)$ consisting of homomorphisms $N_p \colon I \to I_K(\mathfrak f)$ and $\omega_p \colon I \to \mathrm{Gal}(L/K)$, elements $P_p \in I$ and integers $d_p$, such that for all $p, q \in$ `primeCarriers K 𝔣` and all $x \in I$: the Artin symbol `artinSymbol K L 𝔣` (the ray symbol homomorphism sending a height-one prime $v$ to the arithmetic Frobenius at the selected prime above $v$) of $N_p(x)$ equals $\omega_p(x)$; if $\omega_p(x)=1$ then $N_p(x)$ lies in `normRaySubgroup K L 𝔣`, the join of the narrow ray subgroup of $K$ modulo $\mathfrak f$ with the image of the relative norm map from the ideals of $L$ coprime to the extension of $\mathfrak f$; $N_p(P_p)=p$; $\omega_p(P_p)=\sigma^{d_p}$; and there are $b_p, b_q \in I$ with $N_p(b_p)=N_q(b_q)$ and $\omega_p(b_p)=\sigma$. The generator $\sigma$ is produced by the statement rather than prescribed, and the data $N_p,\omega_p,P_p,d_p$ are constrained only at the prime carriers.
--
--   This packages the auxiliary data of Artin's proof of the reciprocity law by crossing with cyclotomic extensions, in the case of a cyclic cubic extension of number fields at an admissible modulus: for each prime coprime to $\mathfrak f$ an auxiliary group of ideals with a norm map to $I_K(\mathfrak f)$ and a symbol map to $\mathrm{Gal}(L/K)$, a distinguished element lifting that prime, and a linking of any two primes by elements of equal norm whose symbol is $\sigma$. It is the input, via reciprocity for cubic extensions, to the statement on character twists of the Artin Frobenius used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField Deep.NTSupply
open LanglandsTunnell.P2.Artin

universe u v

theorem LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_three
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (h3 : Module.finrank K L = 3) (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) :
    ∃ (σ : L ≃ₐ[K] L) (Ip : Type (max u v)) (_ : CommGroup Ip)
      (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣)))
      (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
      (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ),
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ normRaySubgroup K L 𝔣) ∧
      (∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣,
        ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) := by sorry
