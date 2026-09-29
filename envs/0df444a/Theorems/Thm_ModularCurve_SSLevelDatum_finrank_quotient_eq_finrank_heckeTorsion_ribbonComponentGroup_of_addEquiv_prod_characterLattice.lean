-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_finrank_quotient_eq_finrank_heckeTorsion_ribbonComponentGroup_of_addEquiv_prod_characterLattice
-- name    : ModularCurve.SSLevelDatum.finrank_quotient_eq_finrank_heckeTorsion_ribbonComponentGroup_of_addEquiv_prod_characterLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/d4213b5e-d227-5f4f-84d2-538f5ea2373e
-- title:
--   Ribet's count: dim X^{old}/𝔪 X^{old} = dim Ψ[𝔪]
-- statement:
--   Let $M,s,q'$ be positive integers with $M,s$ nonzero, $q'$ and $s$ prime, $q'\ge 5$, $s\neq q'$ and neither $q'$ nor $s$ dividing $M$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $q'$, and assume the sets $\Sigma(Ms)=$ `ssPlaces q' (M*s)` $\kappa$ and $V=\Sigma(M)=$ `ssPlaces q' M` $\kappa$ of supersingular places are finite. Let $X$ be a supersingular level datum `SSLevelDatum q' κ M s` (the two degeneracy maps and Hecke legs between the level-$Ms$ and level-$M$ function fields, integral and carrying supersingular places to supersingular places, an Atkin–Lehner level automorphism preserving $\Sigma(Ms)$, and modular polynomial data satisfying the Kronecker congruence), and assume `X.HeckeLaws`: the edge matrices on $\Sigma(Ms)$ commute with each other, the vertex matrices on $V$ commute with each other, the two degeneracy pushforwards `jointDelta` intertwine the edge and vertex matrices at all primes $\ell\neq s$, and the edge matrices preserve the joint kernel of the pushforwards. Write $\mathbb T=$ `HeckeAlg` $=\mathbb Z[T_\ell:\ell$ prime$]$ for the polynomial Hecke algebra with generators `heckeGen ℓ`. Let $X^{\mathrm{o}}$ be a $\mathbb T$-module with an additive isomorphism $e$ onto $L\times L$, where $L=$ `characterLattice` $V$ is the kernel of the degree map on $V\to\mathbb Z$, such that for every prime $\ell\neq s$ the action of $T_\ell$ corresponds to applying `X.vertexHecke ℓ` to each of the two coordinates, while $T_s$ acts by the companion rule $(x_1,x_2)\mapsto(\,$`X.vertexHecke`$_s x_1-x_2,\ s\,x_1)$. Let $\Psi^{\mathrm{o}}$ be a $\mathbb T$-module with an additive isomorphism $e_\Psi$ onto the ribbon component group of `X.degeneracyData`, i.e. $\operatorname{Hom}_{\mathbb Z}(Z,\mathbb Z)$ modulo the image of the width Gram map, where $Z$ is the ribbon kernel (the intersection of the kernels of the two `jointDelta` maps), and assume that whenever $e_\Psi c$ is the class of $\varphi$, $e_\Psi(T_\ell c)$ is the class of $\varphi$ composed with `heckeKernelMap X.heckeData ℓ`, the restriction of the edge Hecke matrix to $Z$. Finally let $\mathfrak m\subset\mathbb T$ be a maximal ideal that is not eventually Eisenstein (there is no finite set $S$ of primes with $T_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$) and with $T_s^2-1\in\mathfrak m$. Then the $\mathbb T/\mathfrak m$-dimension of $X^{\mathrm{o}}/\mathfrak m X^{\mathrm{o}}$ equals the $\mathbb T/\mathfrak m$-dimension of the $\mathfrak m$-torsion submodule `heckeTorsion` $\Psi^{\mathrm{o}}\,\mathfrak m$, the set of elements killed by every element of $\mathfrak m$.
--
--   This is the dimension comparison used in Ribet's level-lowering argument between the $s$-old part of the character group of the toric part of $J_0(q'M)$ at $q'$ and the $\mathfrak m$-torsion in the group of components at $s$ of the Jacobian of the Shimura curve of discriminant $q's$ and level $M$, here formulated purely in terms of the supersingular degeneracy datum and its ribbon component group. It feeds the estimate [`ModularCurve.pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W`](thm.html#ModularCurve.pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W) in the passage from level $q'Ms$ to level $q'M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_finrank_quotient_eq_finrank_heckeTorsion_ribbonComponentGroup_of_addEquiv_prod_characterLattice.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld

theorem ModularCurve.SSLevelDatum.finrank_quotient_eq_finrank_heckeTorsion_ribbonComponentGroup_of_addEquiv_prod_characterLattice
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    [Fact s.Prime] (hlaws : X.HeckeLaws)
    {Xo : Type} [AddCommGroup Xo] [Module HeckeAlg Xo]
    (e : Xo ≃+ (↥(characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))) × ↥(characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)))))
    (hT : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ s → ∀ x : Xo,
        ((e (heckeGen ℓ • x)).1 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) = (X.vertexHecke ℓ).mulVec ((e x).1 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) ∧
        ((e (heckeGen ℓ • x)).2 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) = (X.vertexHecke ℓ).mulVec ((e x).2 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ))
    (hU : ∀ x : Xo,
        ((e (heckeGen ⟨s, hs⟩ • x)).1 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) =
            (X.vertexHecke ⟨s, hs⟩).mulVec ((e x).1 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) - ((e x).2 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) ∧
        ((e (heckeGen ⟨s, hs⟩ • x)).2 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) = ((s : ℕ) : ℤ) • ((e x).1 : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ))
    {Ψo : Type} [AddCommGroup Ψo] [Module HeckeAlg Ψo]
    (eΨ : Ψo ≃+ ribbonComponentGroup X.degeneracyData)
    (hΨ : ∀ (ℓ : Nat.Primes) (c : Ψo) (φ : Module.Dual ℤ ↥(ribbonKernel X.degeneracyData)),
        eΨ c = ribbonComponentGroupProj X.degeneracyData φ →
          eΨ (heckeGen ℓ • c) = ribbonComponentGroupProj X.degeneracyData (φ ∘ₗ heckeKernelMap X.heckeData ℓ))
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hη : heckeGen ⟨s, hs⟩ ^ 2 - 1 ∈ 𝔪) :
    Module.finrank (HeckeAlg ⧸ 𝔪) (Xo ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo))) =
      Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion Ψo 𝔪) := by sorry
