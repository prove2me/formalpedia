-- Prove2me | Theorems.Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_old_add_ribbon_of_ssLevelDatum_of_two_mul_dvd_of_neZero
-- name    : ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_old_add_ribbon_of_ssLevelDatum_of_two_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/73abf7cf-d77f-5444-8e53-1dfe67d90227
-- title:
--   Toric monodromy bound by old and ribbon parts
-- statement:
--   Fix a prime $p$ and naturals $N,q,q'$ with $q,q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$, $q\neq p$, $q'\neq p$, $p\neq 2$, and a nonzero $D$ divisible by $2Nqq'$. Let $\mathfrak{m}$ be a maximal ideal of `HeckeAlg` $=\mathbb{Z}[T_\ell:\ell\text{ prime}]$ (a polynomial ring on the primes) with $p\in\mathfrak m$, with $T_{q'}^2-1\in\mathfrak m$, not eventually Eisenstein (there is no finite set $S$ of primes with $T_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$), and with $p\nmid q'-1$, $p\mid q-1$. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb{Q}}$ with $q'$, respectively $q$, a nonunit, and write $\kappa$ for the residue field of $A_2$, of characteristic $q$. The Jacobian $J=$ `JZero (N * q' * q)`, the degree-zero divisor class group of the modular function field of level $Nq'q$ over $\overline{\mathbb{Q}}$, carries the Hecke action `heckeModuleBar`. Assume: the inertia subgroup of $A_2$ acts trivially on the $\mathfrak m$-torsion $J[\mathfrak m]$; and $J[\mathfrak m]$ admits a finite field $F$, a ring map $\iota:F\to\mathrm{HeckeAlg}/\mathfrak m$, an $n$, a homomorphism $\rho:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to GL_2(F)$ and a $\mathrm{HeckeAlg}/\mathfrak m$-linear isomorphism $J[\mathfrak m]\cong (F^2)^n$ transporting the Galois action to $\rho$ acting through $\iota$ coordinatewise, such that outside a finite set $S$ of primes containing those dividing $Dp$ one has $T_\ell\equiv\operatorname{tr}\rho(\sigma)$ and $\ell\equiv\det\rho(\sigma)$ modulo $\mathfrak m$ for every Frobenius $\sigma$ at $\ell$, there is $c$ with $\rho(c)^2=1$ and $\det\rho(c)=-1$, $\rho$ is trivial on the Galois group of a finite extension of $\mathbb{Q}$, and $\rho$ has no common eigenvector (for each $v\neq 0$ some $\rho(\sigma)v$ is not a scalar multiple of $v$). Let $X_2$ be a supersingular level datum `SSLevelDatum q κ N q'` satisfying `HeckeLaws` (its edge matrices on the supersingular places of level $Nq'$ and its vertex matrices on those of level $N$ each commute, the two degeneracy pushforwards intertwine them away from $q'$, and the edge matrices preserve their joint kernel). Let $Y_2$ be a Hecke module, finite over $\mathbb{Z}$, identified additively with the ribbon kernel of the degeneracy datum (the intersection of the kernels of the two pushforwards) so that each $T_\ell$ corresponds to the restriction of the edge matrix; and let $X_2^{\mathrm{o}}$ be a Hecke module, finite over $\mathbb{Z}$, identified additively with the square of the degree-zero lattice on the supersingular places of level $N$, on which $T_\ell$ for $\ell\neq q'$ acts by the vertex matrix in each coordinate and $T_{q'}$ acts by $(x_1,x_2)\mapsto(T^{\mathrm{vert}}_{q'}x_1-x_2,\,q'x_1)$. Then the $\mathrm{HeckeAlg}/\mathfrak m$-dimension of the span in $J[\mathfrak m]$ of the part of $J[\mathfrak m]$ lying in `toricMonodromyPart q` for the inertia subgroup of $A_2$ — the span of all $\sigma\!\cdot\! x-x$ with $\sigma$ in that inertia subgroup and $x$ killed by some positive integer coprime to $q$ — is at most $\dim X_2^{\mathrm{o}}/\mathfrak m X_2^{\mathrm{o}}+\dim Y_2/\mathfrak m Y_2$.
--
--   This is the dimension count of Ribet's level-lowering argument at the prime $q$: the character group of $J_0(Nq'q)$ at $q$ sits in an extension of the $q'$-old part by the ribbon (Shimura-curve) part, and tensoring with $\mathrm{HeckeAlg}/\mathfrak m$ bounds the toric $\mathfrak m$-torsion by the two residual dimensions. It feeds the subsequent comparison of toric dimensions used to produce a form of lower level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_old_add_ribbon_of_ssLevelDatum_of_two_mul_dvd_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_old_add_ribbon_of_ssLevelDatum_of_two_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D) (hqp : q ≠ p) (hq'p : q' ≠ p)
    (hp2 : p ≠ 2) (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q]
    [NeZero N] [NeZero q'] [Fact q.Prime] [Fact q'.Prime]
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
            ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    [DecidableEq (IsLocalRing.ResidueField ↥A₂)] [CharP (IsLocalRing.ResidueField ↥A₂) q]
    [Fintype ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A₂))]
    [Fintype ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))]
    [DecidableEq ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A₂))]
    [DecidableEq ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))]
    (X₂ : SSLevelDatum q (IsLocalRing.ResidueField ↥A₂) N q') (hX₂ : X₂.HeckeLaws)
    {Yo₂ : Type} [AddCommGroup Yo₂] [Module HeckeAlg Yo₂] [Module.Finite ℤ Yo₂]
    (eY₂ : Yo₂ ≃+ ↥(CerednikDrinfeld.ribbonKernel X₂.degeneracyData))
    (hY₂ : ∀ (ℓ : Nat.Primes) (m : Yo₂),
      eY₂ (heckeGen ℓ • m) = CerednikDrinfeld.heckeKernelMap X₂.heckeData ℓ (eY₂ m))
    {Xo₂ : Type} [AddCommGroup Xo₂] [Module HeckeAlg Xo₂] [Module.Finite ℤ Xo₂]
    (eX₂ : Xo₂ ≃+ (↥(characterLattice ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))) × ↥(characterLattice ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)))))
    (hT₂ : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' → ∀ x : Xo₂,
        ((eX₂ (heckeGen ℓ • x)).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = (X₂.vertexHecke ℓ).mulVec ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) ∧
        ((eX₂ (heckeGen ℓ • x)).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = (X₂.vertexHecke ℓ).mulVec ((eX₂ x).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ))
    (hU₂ : ∀ x : Xo₂,
        ((eX₂ (heckeGen ⟨q', hq'⟩ • x)).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) =
            (X₂.vertexHecke ⟨q', hq'⟩).mulVec ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) - ((eX₂ x).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) ∧
        ((eX₂ (heckeGen ⟨q', hq'⟩ • x)).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = ((q' : ℕ) : ℤ) • ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ)) :
    letI := heckeModuleBar (N * q' * q)
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
            (toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q))))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (Xo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo₂))) + Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₂))) := by sorry
