-- Prove2me | Theorems.Thm_ModularCurve_finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants
-- name    : ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/bbb20fa6-0dfd-5112-be24-918fe106ef9d
-- title:
--   Ribet's exchange inequality: dim X^{old}+dim Y_{q'}≤dim Y_q
-- statement:
--   Fix a prime $p$ with $p\neq 2$ and integers $N,q,q'$ with $q,q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$, $q\neq p$, $q'\neq p$ and $q'\ge 5$. Let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ containing $p$, not eventually Eisenstein (there is no finite set $S$ of primes with `heckeGen` $\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$), with `heckeGen` $q'^2-1\in\mathfrak m$, and assume $p\mid q-1$ but $p\nmid q'-1$ in $\mathbb Z$. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb Q}$ with $q'$, resp. $q$, a non-unit. Three hypotheses concern $J=$ `JZero` $(Nq'q)$, the degree-zero divisor class group of the geometric modular function field of level $Nq'q$ with its Hecke action: the inertia subgroup at $A_2$ fixes the $\mathfrak m$-torsion $J[\mathfrak m]$ pointwise; $J[\mathfrak m]$ is $\mathfrak m$-linearly isomorphic to $n$ copies of a two-dimensional representation $\rho$ over a finite field $F$ mapped into `HeckeAlg`$/\mathfrak m$ by a ring homomorphism $\iota$, compatibly with the Galois actions, where $\rho$ is unramified outside a finite set of primes all dividing $Nq'qp$ and satisfies $\operatorname{tr}\rho(\sigma)=T_\ell$, $\det\rho(\sigma)=\ell$ modulo $\mathfrak m$ at Frobenius elements there, carries an element $c$ with $\rho(c)^2=1$ and $\det\rho(c)=-1$, factors through a finite extension of $\mathbb Q$, and admits no nonzero vector $v$ with $\rho(\sigma)v$ a scalar multiple of $v$ for all $\sigma$; and `JZero` $(Nq')$ has no lower-level $\mathfrak m$-torsion for any finite set of primes dividing $Nqq'$, i.e. no nonzero $y$ annihilated by the integers in $\mathfrak m$ and by every $T_\ell-b$ lying in $\mathfrak m$ with $\ell$ outside that set. Next, $X_2$ is a supersingular level datum `SSLevelDatum` $q$ for the residue field of $A_2$, level $N$ and auxiliary level $q'$, satisfying `HeckeLaws` (commuting edge and vertex Hecke matrices, equivariance of the two degeneracy pushforwards away from $q'$, stability of the joint kernel), and $X_1$ is likewise a `SSLevelDatum` $q'$ for the residue field of $A_1$, level $N$ and auxiliary level $q$, satisfying `HeckeLaws`. Finitely generated $\mathbb Z$-modules with `HeckeAlg`-action $Yo_2$, $Yo_1$ are identified additively with the ribbon kernels of the degeneracy data of $X_2$, resp. $X_1$ (the intersection of the kernels of the two pushforward maps $E\to V$), the action of each `heckeGen` $\ell$ corresponding to `heckeKernelMap` of the respective Hecke datum; and $Xo_2$ is identified additively with the square of the character lattice (degree-zero functions) on the supersingular places `ssPlaces` $q\,N$ of the residue field of $A_2$, in such a way that for $\ell\neq q'$ each `heckeGen` $\ell$ acts by the vertex Hecke matrix of $X_2$ on both coordinates, while `heckeGen` $q'$ sends $(x,y)$ to $(T^{\mathrm{vert}}_{q'}x-y,\;q'x)$. Finally $\mathcal J$ is a `TwoPlaceTorsionDatum` for $p$ over the degeneracy and Hecke data of $X_2$ and of $X_1$ and the pair $A_1,A_2$ — a finite abelian group killed by $p$ with commuting Hecke and Galois actions, the latter of finite level, together with toric subgroups identified with $\operatorname{Hom}$ of the two ribbon kernels into $\mathbb Z/p$ and specialisation maps from the inertia invariants into the two ribbon component groups — subject to `Laws` $(Nqq'p)\,q'\,q$: good reduction and the Eichler–Shimura relation outside $Nqq'p$ for the first constituent, and the local laws at $q'$ and at $q$ for the first and second constituents respectively. Assuming in addition that $\mathcal J.\mathrm{snd}.W\,\mathfrak m\le\mathcal J.\mathrm{snd}$`.invariants`, the subgroup of elements fixed by the inertia subgroup at $A_2$, the conclusion is the inequality of $\mathrm{HeckeAlg}/\mathfrak m$-dimensions $$\dim Xo_2/\mathfrak m Xo_2+\dim Yo_2/\mathfrak m Yo_2\le \dim Yo_1/\mathfrak m Yo_1.$$
--
--   This is the Shimura-curve half of Ribet's numerical exchange between the two primes $q$ and $q'$ in the case $q\equiv 1 \pmod p$: the old part at $q'$ together with the character group of the fibre in characteristic $q$ is bounded by the character group of the fibre in characteristic $q'$, the comparison being made through the $p$-torsion of the Jacobian of the Shimura curve of discriminant $qq'$ with its two Čerednik–Drinfeld uniformisations. It combines the bound for the first place with the identification of the toric part at the second place, and is used in the level-lowering step that compares monodromy at $q$ and at $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants.lean

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

theorem ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (hqp : q ≠ p) (hq'p : q' ≠ p)
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
          (∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * q' * q * p) ∧
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
    (h𝒥 : 𝒥.Laws (N * q * q' * p) q' q)
    (hunr : 𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants) :
    Module.finrank (HeckeAlg ⧸ 𝔪) (Xo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo₂))) + Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₂))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₁ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₁))) := by sorry
