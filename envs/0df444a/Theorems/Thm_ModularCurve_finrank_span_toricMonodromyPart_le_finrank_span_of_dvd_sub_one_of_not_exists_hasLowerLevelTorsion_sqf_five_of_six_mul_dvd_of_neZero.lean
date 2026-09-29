-- Prove2me | Theorems.Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_span_of_dvd_sub_one_of_not_exists_hasLowerLevelTorsion_sqf_five_of_six_mul_dvd_of_neZero
-- name    : ModularCurve.finrank_span_toricMonodromyPart_le_finrank_span_of_dvd_sub_one_of_not_exists_hasLowerLevelTorsion_sqf_five_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/13a0300d-7870-5e5f-9dd7-39a82a2c850a
-- title:
--   Toric part comparison at q versus q' when p ∣ q-1
-- statement:
--   Fix a prime $p$ with $p \neq 2$, and naturals $N, q, q'$ with $q$ and $q'$ prime, $q' \geq 5$, $q' \neq q$, neither $q$ nor $q'$ dividing $N$, $q \neq p$, $q' \neq p$, $N$ squarefree, and $N q'$, $q$ nonzero; let $D$ be a nonzero natural with $6Nqq' \mid D$. Let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ containing $p$ which is not eventually Eisenstein (there is no finite set $S$ of primes with $X_\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S$), with $X_{q'}^2 - 1 \in \mathfrak m$, and assume $p \nmid q' - 1$ and $p \mid q - 1$ in $\mathbb{Z}$. Let $A_1, A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ with $q'$, resp. $q$, a non-unit of $A_1$, resp. $A_2$, and write $I_1, I_2$ for the images in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of their inertia subgroups. Equip $J =$ `JZero (N * q' * q)`, the degree-zero divisor class group of the modular curve of level $Nq'q$ over $\overline{\mathbb{Q}}$, with the Hecke module structure `heckeModuleBar`, and let $J[\mathfrak m]$ be the submodule of elements killed by $\mathfrak m$. Assume (i) every $\sigma \in I_2$ fixes $J[\mathfrak m]$ pointwise; (ii) there are a finite field $F$, a ring homomorphism $\iota : F \to \mathrm{HeckeAlg}/\mathfrak m$, an $n \in \mathbb{N}$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $2 \times 2$ matrices over $F$, and a $\mathrm{HeckeAlg}/\mathfrak m$-linear isomorphism $e : J[\mathfrak m] \to (\mathrm{Fin}\, n \to \mathrm{Fin}\, 2 \to \mathrm{HeckeAlg}/\mathfrak m)$ carrying the Galois action to $n$ copies of $\rho$ pushed along $\iota$, such that: for some finite set $S$ of naturals containing all primes dividing $Dp$, for every prime $\ell \notin S$, every valuation subring $A$ with $\ell$ a non-unit, and every $\sigma$ which is a Frobenius at $\ell$ for $A$, the images of $X_\ell$ and of $\ell$ in $\mathrm{HeckeAlg}/\mathfrak m$ are the trace and the determinant of $\iota_*\rho(\sigma)$; some $c$ has $\rho(c)^2 = 1$ and $\det \rho(c) = -1$; $\rho$ is trivial on the elements fixing some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$ pointwise; and no nonzero $v \in F^2$ spans a $\rho$-stable line. Then, provided there is no finite set $S$ of primes all dividing $Nqq'$ for which `HasLowerLevelTorsion S 𝔪 (JZero (N * q'))` holds, i.e. for which `JZero (N * q')` contains a nonzero $y$ annihilated by every integer in $\mathfrak m$ and by every $X_\ell - b$ ($\ell \notin S$ prime, $b \in \mathbb{Z}$) lying in $\mathfrak m$, the $\mathrm{HeckeAlg}/\mathfrak m$-dimension of the span inside $J[\mathfrak m]$ of the elements of $J[\mathfrak m]$ lying in `toricMonodromyPart q I₂` is at most that of the span of the elements of $J[\mathfrak m]$ lying in `toricMonodromyPart q' I₁`, where `toricMonodromyPart r I` denotes the Hecke submodule of $J$ spanned by the differences $\sigma x - x$ with $\sigma \in I$ and $x$ killed by some positive integer coprime to $r$.
--
--   This is the interchange step of Ribet's level-lowering argument: the two toric monodromy parts of $J_0(Nqq')[\mathfrak m]$ at the primes $q$ and $q'$ are compared through the character groups of the Shimura curve attached to the quaternion algebra of discriminant $qq'$, the congruence $p \mid q - 1$ entering on the side of $q$. It feeds the corresponding existence statement [`ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero`](thm.html#ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero), and is the edition in which $6Nqq' \mid D$, so that both $2$ and $3$ are invertible on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_span_of_dvd_sub_one_of_not_exists_hasLowerLevelTorsion_sqf_five_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem
ModularCurve.finrank_span_toricMonodromyPart_le_finrank_span_of_dvd_sub_one_of_not_exists_hasLowerLevelTorsion_sqf_five_of_six_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hq'5 : 5 ≤ q') (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D) (hqp : q ≠ p)
    (hq'p : q' ≠ p)
    (hp2 : p ≠ 2) (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q] (hN : Squarefree N)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hnew : heckeGen ⟨q', hq'⟩ ^ 2 - 1 ∈ 𝔪)
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (hq1 : (p : ℤ) ∣ (q : ℤ) - 1)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)
    (hunrJ : letI := heckeModuleBar (N * q' * q)
      ∀ σ ∈ A₂.inertiaSubgroupIn ℚ,
        ∀ x ∈ heckeTorsion (JZero (N * q' * q)) 𝔪, σ • x = x)
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
          ∀ v : Fin 2 → F, v ≠ 0 →
            ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : F, (ρ σ).mulVec v ≠ c • v) :
    letI := heckeModuleBar (N * q')
    letI := heckeModuleBar (N * q' * q)
    (¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) →
        Module.finrank (HeckeAlg ⧸ 𝔪)
            ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
              ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
                (toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q)))))
        ≤ Module.finrank (HeckeAlg ⧸ 𝔪)
            ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
              ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
                (toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q))))) := by sorry
