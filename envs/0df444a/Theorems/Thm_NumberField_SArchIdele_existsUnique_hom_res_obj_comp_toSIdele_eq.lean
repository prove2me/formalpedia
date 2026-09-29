-- Prove2me | Theorems.Thm_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq
-- name    : NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7b0fe8fa-fb53-5b2f-bb4f-773ea4217888
-- title:
--   Unique equivariant map of S∪∞-idèle modules along a tower
-- statement:
--   Let $E\subseteq K\subseteq K'$ be number fields forming a scalar tower with $K/E$ and $K'/E$ Galois, and let $S$ be a finite set of height-one primes of $\mathcal O_E$. Assume given an additive homomorphism $\Phi$ from the product representation [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) of $\mathrm{Gal}(K/E)$ (indexed by the family [`NumberField.SIdele.fibre E K S`](def/NumberField_SIdeleModule.html#L68), whose indices are $\mathrm{Sum.inl}(\mathrm{Sum.inl}\,v)$ for $v\in S$, $\mathrm{Sum.inl}(\mathrm{Sum.inr}\,v)$ for $v\notin S$ and $\mathrm{Sum.inr}\,v$ for infinite places $v$ of $E$) to the additive form of the idèle group $(\mathbb A_K)^\times$, such that: $\Phi$ is injective; its range is the subgroup of those unit idèles which, together with their inverse, are integral at every finite place of $K$ not lying under a prime of $S$; at each $v\in S$, each $v\notin S$ and each infinite place $v$ of $E$, and for every place $w$ and every $y\in\mathrm{Gal}(K/E)$ with $y\cdot w$ equal to the chosen place `above` $v$, the transport isomorphism along $y$ sends the $w$-component of $\Phi x$ to the value at $y$ of the $v$-component of $x$ (taken in the unit group of the valuation ring in the case $v\notin S$, in the completion otherwise); and, for a datum $D$ consisting of a monoid homomorphism from $\mathrm{Gal}(K/E)$ to ring automorphisms of $\mathbb A_K$ compatible with the Galois action on $K$ and continuous, $\Phi$ intertwines the representation action with the induced action of $D$ on units. Assume the same data $\Phi',D'$ for $K'$. Let $JJ\colon(\mathbb A_K)^\times\to(\mathbb A_{K'})^\times$ be a group homomorphism carrying idèles with trivial finite component at every place not under $S$ to idèles with the same property, and satisfying $JJ(D(\pi g')z)=D'(g')(JJ\,z)$, where $\pi$ is restriction of automorphisms to $K$. Then there is a unique morphism $jJ$ of $\mathrm{Gal}(K'/E)$-representations from the restriction along $\pi$ of [`NumberField.SArchIdele.obj E K S`](def/NumberField_SArchIdeleModule.html#L32) to [`NumberField.SArchIdele.obj E K' S`](def/NumberField_SArchIdeleModule.html#L32) with $\Phi'(\mathrm{toSIdele}(jJ\,y))=JJ(\Phi(\mathrm{toSIdele}\,y))$ for all $y$.
--
--   This is the tower square for the $S$-and-archimedean idèle modules: it produces the middle vertical arrow, over a given map $JJ$ of idèle groups, in a morphism of the short exact sequences relating $S$-units, $S$-idèles and the $S$-idèle class group for $K$ and for $K'$. It is used in the construction of the cohomology classes and the pairings on the Shafarevich groups attached to the tower, where naturality of the connecting homomorphisms is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_SArchIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField M4aHerbrand
open scoped NumberField.PlaceTransport

theorem NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq
    (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra E K] [Algebra E K'] [Algebra K K'] [IsScalarTower E K K'] [IsGalois E K] [IsGalois E K']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦout : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
            (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦinf : ∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.ArchIdele.above E K v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K v).Completion))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    (hΦeq : ∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))

    (Φ' : NumberField.SIdele.obj E K' S →+ Additive (AdeleRing (𝓞 K') K')ˣ)
    (hΦinj' : Function.Injective Φ')
    (hΦrange' : Φ'.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K') K' {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletion K')ˣ) : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦout' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K')ˣ) :
            (NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K') : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦinf' : ∀ (x : NumberField.SIdele.obj E K' S) (v : InfinitePlace E) (w : InfinitePlace K') (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.ArchIdele.above E K' v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K' v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K' v).Completion))
    (D' : IdeleGaloisDescent (𝓞 K') E K')
    (hΦeq' : ∀ (g : K' ≃ₐ[E] K') (x : NumberField.SIdele.obj E K' S),
      Φ' ((NumberField.SIdele.obj E K' S).ρ g x) = Additive.ofMul (D'.unitsAct g (Additive.toMul (Φ' x))))

    (JJ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K') K')ˣ)
    (hJJ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → finPart w z = 1) →
      ∀ w' : HeightOneSpectrum (𝓞 K'), w'.under (𝓞 E) ∉ S → finPart w' (JJ z) = 1)
    (hJJeq : ∀ (g' : K' ≃ₐ[E] K') (z : (AdeleRing (𝓞 K) K)ˣ),
      JJ (D.unitsAct (AlgEquiv.restrictNormalHom K g') z) = D'.unitsAct g' (JJ z)) :
    ∃! jJ : Rep.res (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[E] K') →* (K ≃ₐ[E] K)) (NumberField.SArchIdele.obj E K S) ⟶
        NumberField.SArchIdele.obj E K' S,
      ∀ y : NumberField.SArchIdele.obj E K S,
        Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom (jJ.hom y)) =
          Additive.ofMul (JJ (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) := by sorry
