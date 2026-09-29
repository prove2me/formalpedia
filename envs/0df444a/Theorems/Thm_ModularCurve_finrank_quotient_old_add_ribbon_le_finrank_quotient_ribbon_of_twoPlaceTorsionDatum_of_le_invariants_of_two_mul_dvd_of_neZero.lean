-- Prove2me | Theorems.Thm_ModularCurve_finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants_of_two_mul_dvd_of_neZero
-- name    : ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants_of_two_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/3161e573-1f5e-512c-955f-b7aecbcf256b
-- title:
--   Rank inequality between old-plus-ribbon and ribbon parts at two places
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N, q, q'$ be natural numbers with $q, q'$ prime, $q' \neq q$, neither dividing $N$, both different from $p$, with $q' \geq 5$, and let $D$ be a nonzero natural number with $2Nqq' \mid D$. Let $\mathfrak m$ be a maximal ideal of the Hecke algebra $\mathbb T =$ `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$ containing $p$ and containing $\mathrm{heckeGen}\,q'^2 - 1$, and assume $\mathfrak m$ is not eventually Eisenstein, i.e. there is no finite set $S$ of primes with $\mathrm{heckeGen}\,\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S$; assume $p \mid q-1$ and $p \nmid q'-1$ in $\mathbb Z$. Let $A_1, A_2$ be valuation subrings of $\overline{\mathbb Q}$ with $q'$, respectively $q$, a nonunit of $A_1$, respectively $A_2$. On $J = \mathrm{Pic}^0$ of the level-$Nq'q$ geometric modular function field over $\overline{\mathbb Q}$, with its Hecke-algebra structure, two hypotheses are imposed: the $\mathfrak m$-torsion submodule (the elements killed by every element of $\mathfrak m$) is fixed pointwise by the inertia subgroup of $A_2$ in $\mathbb Q$, and it is big-image residual of the following explicit shape: there are a finite field $F$, a ring homomorphism $\iota : F \to \mathbb T/\mathfrak m$, an $n \in \mathbb N$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $2 \times 2$ matrices over $F$, and a $\mathbb T/\mathfrak m$-linear isomorphism $e$ of the $\mathfrak m$-torsion with $n$ copies of $(\mathbb T/\mathfrak m)^2$ carrying the Galois action to coordinatewise multiplication by $\iota(\rho\sigma)$, such that for some finite set $S$ of primes containing every prime divisor of $Dp$, and every prime $\ell \notin S$, every valuation subring over $\ell$ and every Frobenius $\sigma$ there, the image of $\mathrm{heckeGen}\,\ell$ in $\mathbb T/\mathfrak m$ is $\mathrm{tr}\,\iota(\rho\sigma)$ and the image of $\ell$ is $\det \iota(\rho\sigma)$; some $c$ has $\rho(c)^2 = 1$ and $\det \rho(c) = -1$; $\rho$ is trivial on the Galois group of a finite extension of $\mathbb Q$; and no nonzero $v \in F^2$ satisfies $\rho(\sigma)v \in F v$ for all $\sigma$. It is further assumed that level $Nq'$ carries no lower-level torsion for $\mathfrak m$: for no finite set $S$ of primes dividing $Nqq'$ is there a nonzero $y$ in $\mathrm{Pic}^0$ at level $Nq'$ annihilated by every integer in $\mathfrak m$ and by $\mathrm{heckeGen}\,\ell - b$ whenever $\ell \notin S$ and $\mathrm{heckeGen}\,\ell - b \in \mathfrak m$. Let $X_2$ be a supersingular level datum for $q$ over the residue field of $A_2$ with levels $(N, q')$, and $X_1$ one for $q'$ over the residue field of $A_1$ with levels $(N, q)$, both satisfying `HeckeLaws`. Let $Yo_2$, $Yo_1$ be $\mathbb T$-modules, finite over $\mathbb Z$, with additive isomorphisms onto the ribbon kernels of the degeneracy data of $X_2$, $X_1$ (the intersection of the kernels of the two pushforward maps on divisor groups of supersingular places) intertwining each $\mathrm{heckeGen}\,\ell$ with the corresponding edge Hecke matrix acting on the ribbon kernel, and let $Xo_2$ be a $\mathbb T$-module, finite over $\mathbb Z$, with an additive isomorphism onto the square of the degree-zero character lattice on the supersingular places of level $N$ in the residue field of $A_2$, under which $\mathrm{heckeGen}\,\ell$ acts on both coordinates by the vertex Hecke matrix of $X_2$ for $\ell \neq q'$, while $\mathrm{heckeGen}\,q'$ sends $(x,y)$ to $(T_{q'}x - y,\ q' x)$. Finally let $\mathcal J$ be a two-place torsion datum for $p$ over the pair of degeneracy and Hecke data $(X_2, X_1)$ and the places $A_1, A_2$, satisfying the laws for $(Dp, q', q)$ — good reduction outside $Dp$ together with the Eichler–Shimura relation for its first component, and the local laws at $q'$ and at $q$ for its first and second components — and assume the subgroup $\mathcal J.\mathrm{snd}.W\ \mathfrak m$ is contained in the inertia invariants $\bigcap_{\sigma \in I(A_2)} \ker(\mathcal J.\mathrm{gal}\,\sigma - \mathrm{id})$. Then, over the residue field $\mathbb T/\mathfrak m$, $$\dim (Xo_2/\mathfrak m\,Xo_2) + \dim (Yo_2/\mathfrak m\,Yo_2) \le \dim (Yo_1/\mathfrak m\,Yo_1).$$
--
--   This is the Shimura-curve half of Ribet's multiplicity count governing the level-lowering switch between the two auxiliary primes $q$ and $q'$, in the case $q \equiv 1 \pmod p$: the old part at $q$ together with the character-group (ribbon) contribution at $q$ is bounded by the ribbon contribution at $q'$, all measured by mod-$\mathfrak m$ dimensions. It feeds the comparison of toric monodromy parts used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants_of_two_mul_dvd_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants_of_two_mul_dvd_of_neZero
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
    (hreg : letI := heckeModuleBar (N * q')
      ¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q')))
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
        ((eX₂ (heckeGen ⟨q', hq'⟩ • x)).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = ((q' : ℕ) : ℤ) • ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ))
    [DecidableEq (IsLocalRing.ResidueField ↥A₁)] [CharP (IsLocalRing.ResidueField ↥A₁) q']
    [Fintype ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    (X₁ : SSLevelDatum q' (IsLocalRing.ResidueField ↥A₁) N q) (hX₁ : X₁.HeckeLaws)
    {Yo₁ : Type} [AddCommGroup Yo₁] [Module HeckeAlg Yo₁] [Module.Finite ℤ Yo₁]
    (eY₁ : Yo₁ ≃+ ↥(CerednikDrinfeld.ribbonKernel X₁.degeneracyData))
    (hY₁ : ∀ (ℓ : Nat.Primes) (m : Yo₁),
      eY₁ (heckeGen ℓ • m) = CerednikDrinfeld.heckeKernelMap X₁.heckeData ℓ (eY₁ m))
    (hq'5 : 5 ≤ q')
    (𝒥 : CerednikDrinfeld.TwoPlaceTorsionDatum p X₂.degeneracyData X₂.heckeData X₁.degeneracyData X₁.heckeData A₁ A₂)
    (h𝒥 : 𝒥.Laws (D * p) q' q)
    (hunr : 𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants) :
    Module.finrank (HeckeAlg ⧸ 𝔪) (Xo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo₂))) + Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₂))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₁ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₁))) := by sorry
