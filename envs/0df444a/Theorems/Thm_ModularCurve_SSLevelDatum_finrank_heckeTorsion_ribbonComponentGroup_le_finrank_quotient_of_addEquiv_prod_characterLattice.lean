-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice
-- name    : ModularCurve.SSLevelDatum.finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/64144b9b-5944-533c-b583-1329960a29a7
-- title:
--   Eisenstein cokernel bound for the ribbon component group
-- statement:
--   Fix natural numbers $M,s,q'$ with $M,s$ nonzero, $q'$ and $s$ prime, $q'\ge 5$, $s\ne q'$, and $q'\nmid M$, $s\nmid M$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $q'$, and assume the sets $\Sigma(Ms)$, $\Sigma(M)$ of supersingular places (places of the level-$N$ modular function field over $\kappa$ satisfying `IsSupersingularPlace`) are finite. Let $X$ be a supersingular level datum of levels $Ms\rightrightarrows M$ over $\kappa$: the level-$M$ and level-$s$ $j$-functions lie in the level-$Ms$ function field, the two degeneracy morphisms and all Hecke legs are integral, both degeneracy maps send $\Sigma(Ms)$ into $\Sigma(M)$, an Atkin–Lehner level automorphism is given which preserves $\Sigma(Ms)$, and modular polynomial data satisfying a Kronecker congruence is given. Assume `X.HeckeLaws`: the edge matrices commute with one another, the vertex matrices commute with one another, for $\ell\neq s$ the edge matrices intertwine with the vertex matrices through both maps `jointDelta`, and the edge matrices preserve the joint kernel of the `jointDelta`. Write $\mathbb T=\mathbb Z[T_\ell:\ell\text{ prime}]$ for `HeckeAlg`, the polynomial ring on the primes, with $T_\ell=$ `heckeGen`. Let $Xo$ be a $\mathbb T$-module together with an additive isomorphism $e$ onto $L\times L$, where $L$ is the character lattice of $\Sigma(M)$, i.e. the degree-zero functions $\Sigma(M)\to\mathbb Z$, such that for every prime $\ell\ne s$ both coordinates of $e(T_\ell x)$ are obtained from those of $e(x)$ by multiplication by the vertex Hecke matrix `X.vertexHecke ℓ`, while for $\ell=s$ one has $e(T_s x)=\bigl(\,\mathrm{X.vertexHecke}\ s\cdot (ex)_1-(ex)_2,\; s\,(ex)_1\bigr)$ (a companion-matrix law). Let $\Psi o$ be a $\mathbb T$-module with an additive isomorphism $e_\Psi$ onto the ribbon component group of `X.degeneracyData`, that is $\operatorname{Hom}_{\mathbb Z}(Z,\mathbb Z)$ modulo the image of the width Gram map, $Z$ being the joint kernel `ribbonKernel`, such that for every prime $\ell$, whenever $e_\Psi(c)$ is the class of a functional $\varphi$ on $Z$, $e_\Psi(T_\ell c)$ is the class of $\varphi$ composed with the restriction `heckeKernelMap X.heckeData ℓ` of the edge Hecke operator to $Z$. Finally let $\mathfrak m$ be a maximal ideal of $\mathbb T$ which is not eventually Eisenstein, i.e. for no finite set $S$ of primes does $T_\ell-(\ell+1)$ lie in $\mathfrak m$ for all $\ell\notin S$. The conclusion is the inequality of $\mathbb T/\mathfrak m$-dimensions $\dim \Psi o[\mathfrak m]\le \dim Xo/\mathfrak m\,Xo$, where $\Psi o[\mathfrak m]$ is the submodule of elements killed by every element of $\mathfrak m$.
--
--   This is one half — the inequality coming from an Eisenstein cokernel, with no congruence condition at $s$ imposed — of Ribet's comparison between the $\mathfrak m$-torsion in the component group at $s$ of the Shimura curve of discriminant $q's$ and level $M$ and the old part of the modular lattice at level $Ms$. It feeds the toric-part estimate used in the level-lowering step, being cited in the analysis of the two-place torsion datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open CerednikDrinfeld

theorem ModularCurve.SSLevelDatum.finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice
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
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (heis : ¬ IsEventuallyEisenstein 𝔪) :
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion Ψo 𝔪) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (Xo ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo))) := by sorry
