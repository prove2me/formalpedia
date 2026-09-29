-- Prove2me | Theorems.Thm_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero
-- name    : NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/731face6-7eda-5363-bb13-7d388e788722
-- title:
--   Idèle classes trivial off S descend uniquely to S-idèles
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, $G = K \simeq_{\mathrm{alg}[E]} K$ its Galois group, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. Let $D$ be an `IdeleGaloisDescent` datum for $(\mathcal{O}_K, E, K)$, that is, a monoid homomorphism from $G$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_K, K)$ which is compatible with the structure map from $K$ and continuous in each element; assume the given multiplicative-distributive action of $G$ on the unit group of the adèle ring is the one induced by $D$ on units. Let $\Psi$ be a morphism of $\mathbb{Z}$-representations of $G$ from [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) (the product representation attached to the family `fibre E K S`) to the additively written representation on $(\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$, assumed injective on underlying groups and with image exactly the subgroup `unitIdelesOutside` of those $y$ such that for every height-one prime $w$ of $\mathcal{O}_K$ whose prime below in $\mathcal{O}_E$ is not in $S$, both $y_w$ and $(y^{-1})_w$ lie in the $w$-adic valuation ring. Let $\mathrm{prG}\,w$, for each $w$, be a morphism from the restriction of the idèle-unit representation along the inclusion of the decomposition subgroup $\mathrm{decomp}\,E\,K\,w$ into $G$ to the representation on $(K_w)^\times$, assumed to send (the additive copy of) $y$ to (the additive copy of) its $w$-component $\mathrm{finPart}\ w\ y$. Finally let $x \in H^2(G, (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times)$ be such that for every $w$ whose contraction to $\mathcal{O}_E$ differs from every prime in $S$, the map on $H^2$ induced by the pair (inclusion of $\mathrm{decomp}\,E\,K\,w$, $\mathrm{prG}\,w$) annihilates $x$. Then there is exactly one class $z \in H^2(G, \mathtt{SIdele.obj}\,E\,K\,S)$ whose image under the coefficient map induced by $\Psi$ (with the identity on $G$) equals $x$.
--
--   This is the standard comparison between the cohomology of the $S$-idèles and of the full idèle group in degree $2$: a two-dimensional idèle class with vanishing local components outside the primes above $S$ comes from a unique $S$-idèle class, the quotient $\mathbb{I}_K/J^S_K$ being a permutation module on the places off $S$. It is used in the construction of the capitulation class, via [`NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation`](thm.html#NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsDedekindDomain NumberField CategoryTheory groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x = 0) :
    ∃! z : groupCohomology (NumberField.SIdele.obj E K S) 2,
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2).hom z = x := by sorry
