-- Prove2me | Theorems.Thm_ModularCurve_natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_isMaximal_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- name    : ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_isMaximal_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/885546a9-df12-58a0-a3e0-7d9ca837d7d9
-- title:
--   Interchange inequality for toric parts of the 𝔪-torsion
-- statement:
--   Fix a prime $p$ and natural numbers $N,q,q'$ with $q$ and $q'$ prime, $q'\ge 5$, $q\nmid N$, $q'\nmid N$, $q'\ne q$, $q\ne p$, $q'\ne p$, $p\ne 2$ and $N$ squarefree, together with a nonzero $D$ divisible by $6Nqq'$. Let $\mathrm{HeckeAlg}=\mathbb Z[T_\ell:\ell\ \text{prime}]$ (the polynomial ring $\mathbb{Z}[X_\ell]$ on the primes, $T_\ell=$ `heckeGen` $\ell$), acting on $J_0(M)=\mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb Q}$ through `heckeModuleBar`, and let $\mathfrak m$ be a maximal ideal containing $p$ and $T_{q'}^2-1$ which is not eventually Eisenstein (no finite set $S$ of primes with $T_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$). Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb Q}$ with $q'$, resp. $q$, a nonunit, and $I_1,I_2$ their inertia subgroups inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Assume $p\nmid q'-1$, $p\mid q-1$, that $I_2$ fixes $J[\mathfrak m]=$ `heckeTorsion` $(J_0(Nq'q))$ $\mathfrak m$ pointwise, and the decomposition datum: there are a finite field $F$, a ring map $\iota:F\to\mathrm{HeckeAlg}/\mathfrak m$, an $n$, a monoid map $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $2\times 2$ matrices over $F$ and an $\mathrm{HeckeAlg}/\mathfrak m$-linear isomorphism $e:J[\mathfrak m]\simeq (F^2)^{\oplus n}$-shaped module $(\mathrm{Fin}\,n\to\mathrm{Fin}\,2\to \mathrm{HeckeAlg}/\mathfrak m)$ carrying the Galois action to the $n$-fold sum of $\rho$ pushed along $\iota$; outside a finite set $S$ of primes containing all divisors of $Dp$, $T_\ell$ and $\ell$ have images in $\mathrm{HeckeAlg}/\mathfrak m$ equal to the trace and determinant of $\rho(\sigma)$ for any $\sigma$ that is a Frobenius at $\ell$ for a valuation subring over $\ell$; some $c$ has $\rho(c)^2=1$, $\det\rho(c)=-1$; $\rho$ is trivial on the subgroup fixing some finite extension of $\mathbb Q$; and no nonzero $v\in F^2$ is an eigenvector of all $\rho(\sigma)$. Then, provided there is no finite set $S$ of primes all dividing $Nqq'$ with `HasLowerLevelTorsion` $S$ $\mathfrak m$ $(J_0(Nq'))$, i.e. no nonzero $y\in J_0(Nq')$ killed by every integer in $\mathfrak m$ and by every $T_\ell-b$ ($\ell\notin S$ prime, $b\in\mathbb Z$) lying in $\mathfrak m$, one has $$\#\bigl(\mathcal T_q(I_2)\cap J[\mathfrak m]\bigr)\le \#\bigl(\mathcal T_{q'}(I_1)\cap J[\mathfrak m]\cap\ker\delta_0\cap\ker\delta_1\bigr),$$ where $\mathcal T_r(I)$ is the $\mathrm{HeckeAlg}$-span of the elements $\sigma x-x$ with $\sigma\in I$ and $x$ killed by some positive integer coprime to $r$, and $\delta_0,\delta_1$ are the two degeneracy pushforwards $J_0(Nq'q)\to J_0(Nq')$ in level $q$.
--
--   This is the counting form of the interchange step in Ribet's level-lowering argument: it compares the $q$-adic and $q'$-adic toric parts of the $\mathfrak m$-torsion of $J_0(Nq'q)$ at an abstract non-Eisenstein maximal ideal of the Hecke algebra, the case of the ideal attached to a newform being an instance. It feeds the corresponding statement with the maximality hypothesis packaged differently, [`ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero`](thm.html#ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_isMaximal_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_isMaximal_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hq'5 : 5 ≤ q') (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D) (hqp : q ≠ p) (hq'p : q' ≠ p)
    (hp2 : p ≠ 2) (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q] (hN : Squarefree N)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hnew : heckeGen ⟨q', hq'⟩ ^ 2 - 1 ∈ 𝔪)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)
    (hblr : letI := heckeModuleBar (N * q' * q)
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ι : F →+* HeckeAlg ⧸ 𝔪) (n : ℕ)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
        (e : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → Fin 2 → HeckeAlg ⧸ 𝔪)),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)),
            σ • (w : JZero (N * q' * q)) = ↑(e.symm fun i => ((ρ σ).map ι).mulVec (e w i))) ∧
          (∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ D * p) ∧
            ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
              A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
                Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
                  Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det) ∧
          (∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ c * ρ c = 1 ∧ (ρ c).det = -1) ∧
          GaloisFactorsThroughFiniteLevel ρ ∧
          ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (hq1 : (p : ℤ) ∣ (q : ℤ) - 1)
    (hunrJ : letI := heckeModuleBar (N * q' * q)
      ∀ σ ∈ A₂.inertiaSubgroupIn ℚ, ∀ x ∈ heckeTorsion (JZero (N * q' * q)) 𝔪, σ • x = x) :
    letI := heckeModuleBar (N * q')
    letI := heckeModuleBar (N * q' * q)
    (¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) →
      Nat.card ↥(toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) ⊓
          heckeTorsion (JZero (N * q' * q)) 𝔪)
        ≤ Nat.card ↥((toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ) ⊓
            heckeTorsion (JZero (N * q' * q))
              𝔪).toAddSubgroup ⊓
            (degeneracyPushforwardPair (N * q') q 0).ker ⊓ (degeneracyPushforwardPair (N * q') q 1).ker) := by sorry
