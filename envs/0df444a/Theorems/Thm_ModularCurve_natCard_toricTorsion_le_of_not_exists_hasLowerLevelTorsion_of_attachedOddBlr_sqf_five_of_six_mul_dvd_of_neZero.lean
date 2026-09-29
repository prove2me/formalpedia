-- Prove2me | Theorems.Thm_ModularCurve_natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- name    : ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/3e60a29e-c392-5731-bcd8-f9d1e3a0b35d
-- title:
--   Toric torsion inequality at a q'-new eigenform, q' not≡ 1
-- statement:
--   Let $p$, $q$, $q'$ be primes with $q' \ge 5$, $q' \neq q$, $q \neq p$, $q' \neq p$, let $N$ be squarefree with $q \nmid N$ and $q' \nmid N$ (and $Nq' \neq 0$), and let $D \neq 0$ satisfy $6Nqq' \mid D$. Let $g$ be a weight-two cusp form on $\Gamma_0(Nqq')$ that is a normalised eigenform (first $q$-coefficient $1$, multiplicativity on coprime indices, and the two Hecke recursions at primes prime to, respectively dividing, the level), with $a_q(g)^2 = 1$ and $a_{q'}(g)^2 = 1$. Let $\mathcal{O} \subseteq \mathbb{C}$ be a subring containing all $a_\ell(g)$ for $\ell$ prime, $\varphi : \mathcal{O} \to k$ a ring homomorphism to a field, and $\mathfrak{m} \subset \mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ the kernel of the $\mathbb{Z}$-algebra map $X_\ell \mapsto \varphi(a_\ell(g))$; assume $\mathfrak{m}$ maximal, $p \in \mathfrak{m}$, and $\mathfrak{m}$ not eventually Eisenstein (there is no finite set $S$ of primes with $X_\ell - (\ell+1) \in \mathfrak{m}$ for all $\ell \notin S$). Assume $p \nmid q'-1$ and $p \mid q-1$ in $\mathbb{Z}$. Let $A_1$, $A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ with $q'$, respectively $q$, a non-unit, and write $J = \mathrm{Pic}^0$ of the base-changed full modular function field of level $Nq'q$, with its $\mathbb{T}$-action, and $J[\mathfrak{m}]$ for the $\mathfrak{m}$-torsion submodule. Two hypotheses on $J[\mathfrak{m}]$ are imposed: first, a decomposition datum consisting of a finite field $F$, a ring map $\iota : F \to \mathbb{T}/\mathfrak{m}$, an integer $n$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $2 \times 2$ matrices over $F$, and a $\mathbb{T}/\mathfrak{m}$-linear isomorphism $J[\mathfrak{m}] \cong (\mathbb{T}/\mathfrak{m})^{2n}$ carrying the Galois action to $\rho$ applied blockwise through $\iota$, such that outside a finite set of primes containing all divisors of $Dp$ the images of $X_\ell$ and of $\ell$ in $\mathbb{T}/\mathfrak{m}$ are the trace and determinant of $\iota(\rho(\sigma))$ for every Frobenius $\sigma$ at $\ell$ relative to any valuation subring over $\ell$, such that some $c$ has $\rho(c)^2 = 1$ and $\det \rho(c) = -1$, such that $\rho$ is trivial on the subgroup fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, and such that no nonzero vector of $F^2$ is an eigenvector for all $\rho(\sigma)$; second, that the inertia subgroup attached to $A_2$ acts trivially on $J[\mathfrak{m}]$. The conclusion is: if there is no finite set $S$ of primes all dividing $Nqq'$ admitting a nonzero element $y$ of $\mathrm{Pic}^0$ at level $Nq'$ killed by every integer of $\mathfrak{m}$ and by every $X_\ell - b$ lying in $\mathfrak{m}$ with $\ell \notin S$ and $b \in \mathbb{Z}$, then the cardinality of the intersection of $J[\mathfrak{m}]$ with the $q$-toric monodromy part at $A_2$ (the $\mathbb{T}$-span of the differences $\sigma \cdot x - x$ for $\sigma$ in the inertia group of $A_2$ and $x$ killed by some positive integer prime to $q$) is at most the cardinality of the intersection of $J[\mathfrak{m}]$ with the $q'$-toric monodromy part at $A_1$ and with the kernels of both degeneracy push-forwards from level $Nq'q$ to level $Nq'$.
--
--   This is the interchange inequality between the $q$-toric and the $q'$-toric parts of the $\mathfrak{m}$-torsion of the Jacobian at level $Nq'q$, in the form used in Ribet's level-lowering argument, specialised from an abstract maximal ideal of the Hecke algebra to the maximal ideal cut out by the residual eigensystem of a weight-two form on $\Gamma_0(Nqq')$, with the auxiliary modulus $D$ divisible by $6Nqq'$ recording the primes excluded from the Frobenius conditions. It feeds the production of lower-level $\mathfrak{m}$-torsion, cited by [`WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five`](thm.html#WeierstrassCurve.exists_hasLowerLevelTorsion_jZero_of_twoNewEigenformCongruence_sqf_five).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.natCard_toricTorsion_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hq'5 : 5 ≤ q') (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D) (hqp : q ≠ p) (hq'p : q' ≠ p)
    (hq'N : ¬ q' ∣ N) [NeZero (N * q')] (hN : Squarefree N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 (N * q * q')) 2)
    (hg : g.IsNormalizedEigenform) (hgq : g.IsNewAt q) (hgq' : g.IsNewAt q')
    (k : Type) [Field k] (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff g ℓ ∈ 𝒪) (φ : 𝒪 →+* k)
    (hmax : (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)).IsMaximal)
    (hp : (p : HeckeAlg) ∈ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))
    (heis : ¬ IsEventuallyEisenstein (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)))
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (hq1 : (p : ℤ) ∣ (q : ℤ) - 1)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q) [NeZero q]
    (hblr : letI := heckeModuleBar (N * q' * q)
      ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (ι : F →+* HeckeAlg ⧸ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)) (n : ℕ)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
        (e : ↥(heckeTorsion (JZero (N * q' * q)) (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)))
          ≃ₗ[HeckeAlg ⧸ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)]
            (Fin n → Fin 2 → HeckeAlg ⧸ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (w : ↥(heckeTorsion (JZero (N * q' * q)) (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)))),
            σ • (w : JZero (N * q' * q)) = ↑(e.symm fun i => ((ρ σ).map ι).mulVec (e w i))) ∧
          (∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ D * p) ∧
            ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
              A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
                Ideal.Quotient.mk (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))
                    (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
                  Ideal.Quotient.mk (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))
                    ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det) ∧
          (∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ c * ρ c = 1 ∧ (ρ c).det = -1) ∧
          GaloisFactorsThroughFiniteLevel ρ ∧
          ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    (hunrJ : letI := heckeModuleBar (N * q' * q)
      ∀ σ ∈ A₂.inertiaSubgroupIn ℚ,
        ∀ x ∈ heckeTorsion (JZero (N * q' * q)) (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)), σ • x = x) :
    letI := heckeModuleBar (N * q')
    letI := heckeModuleBar (N * q' * q)
    (¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)) (JZero (N * q'))) →
      Nat.card ↥(toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) ⊓
          heckeTorsion (JZero (N * q' * q)) (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩)))
        ≤ Nat.card ↥((toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ) ⊓
            heckeTorsion (JZero (N * q' * q))
              (eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff g ℓ, h𝒪 ℓ⟩))).toAddSubgroup ⊓
            (degeneracyPushforwardPair (N * q') q 0).ker ⊓ (degeneracyPushforwardPair (N * q') q 1).ker) := by sorry
