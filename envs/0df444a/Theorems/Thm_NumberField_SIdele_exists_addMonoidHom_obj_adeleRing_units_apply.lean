-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
-- name    : NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/0b8c45ff-42cb-5f23-ac7e-2b52cb1d97aa
-- title:
--   Coordinatewise equivariant embedding of the S-idèle module
-- statement:
--   Let $E$ and $K$ be number fields with $K/E$ Galois, $S$ a finite set of nonzero primes of $\mathcal O_E$, and let $D$ consist of a monoid homomorphism from $\operatorname{Gal}(K/E)$ to the ring automorphisms of $\mathbb A_K =$ `AdeleRing (𝓞 K) K`, each automorphism continuous and agreeing with $g$ on the image of $K$. The representation `SIdele.obj E K S` of $\operatorname{Gal}(K/E)$ over $\mathbb Z$ is the product, over $v\in S$, over $v\notin S$ and over the infinite places $v$ of $E$, of the coinduced modules along the inclusion of the decomposition group of the chosen place `above E K v` of $K$, with coefficients the local units, the units of the local integers, and the archimedean local units respectively. The assertion is that there is an injective additive homomorphism $\Phi$ from this product to $\operatorname{Additive} \mathbb A_K^\times$ whose range is the subgroup `AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}`, i.e. the idèles $\delta$ with $\delta_w$ and $(\delta^{-1})_w$ integral at every finite $w$ not above $S$; which intertwines the action on the product with $g\mapsto$ the automorphism of $\mathbb A_K^\times$ induced by $D$'s automorphism at $g$; which sends the diagonal image of an element of `sUnitsRep E K S` to the principal idèle of the corresponding element of $K^\times$; and whose coordinates are the values of the coinduced functions: for every $x$, every $v$ (in $S$, outside $S$, or infinite), every place $w$ of $K$ and every $y\in\operatorname{Gal}(K/E)$ with $y\cdot w =$ the chosen place above $v$, transporting the $w$-coordinate of $\Phi(x)$ along $y$ gives the value at $y$ of the $v$-component of $x$, with the unit of the local integers, respectively the local unit, coerced into the completion.
--
--   This is the place-by-place description of the idèle group of $K$ as a product of modules coinduced from the decomposition groups, in the form needed to compare Shapiro's isomorphism with local coordinates. It is used in the cohomological computations for the idèle and idèle-class modules and in the level-lowering arithmetic built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) ∧

      (∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.PlaceAbove.above E K v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
          ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
            ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K)) ∧
      (∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.PlaceAbove.above E K v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
          (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
            ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
              (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K)) ∧
      (∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
        (hy : y • w = NumberField.ArchIdele.above E K v),
        NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
          ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
            (NumberField.ArchIdele.above E K v).Completion)) := by sorry
