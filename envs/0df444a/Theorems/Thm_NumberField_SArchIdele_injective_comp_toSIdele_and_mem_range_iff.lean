-- Prove2me | Theorems.Thm_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff
-- name    : NumberField.SArchIdele.injective_comp_toSIdele_and_mem_range_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1857eaee-a552-520b-a9e2-44b7777340ea
-- title:
--   Image of the S∪∞-idèle module in the idèles
-- statement:
--   Let $E\subseteq K$ be number fields with $K/E$ Galois, let $S$ be a finite set of height-one primes of $\mathcal O_E$, and let $\Phi$ be an additive homomorphism from [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) (the $\mathbb Z[\mathrm{Gal}(K/E)]$-representation obtained as the product of the representations `fibre E K S` over the index type $(\{v\in S\}\sqcup\{v\notin S\})\sqcup \mathrm{InfinitePlace}\,E$) to the additive group $\mathrm{Additive}\,(\mathbb A_K)^\times$ of units of the adèle ring of $K$. Assume: $\Phi$ is injective; the range of $\Phi$ is the additive subgroup corresponding to [`NumberField.AdeleRing.unitIdelesOutside`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) for the set $\{w\mid w\cap\mathcal O_E\in S\}$, that is, the group of idèles $\delta$ such that for every finite place $w$ of $K$ lying under a prime outside $S$ both $\delta_w$ and $(\delta^{-1})_w$ lie in $\mathcal O_{K_w}$; and three coordinate clauses, each saying that for $x$ in the module, an index $v$, a place $w$ of $K$ and $y\in\mathrm{Gal}(K/E)$ with $y\cdot w$ equal to the chosen place `above` $v$, the transport isomorphism attached to $y$ carries the $w$-component of $\Phi x$ to the value at $y$ of the corresponding component of $x$ — for $v\in S$ the component lies in $(K_{\mathrm{above}\,v})^\times$ (clause `hΦS`), for $v\notin S$ in $\mathcal O_{\mathrm{above}\,v}^\times$ (clause `hΦout`), and for $v$ an infinite place of $E$ in the units of the completion at `above` $v$ (clause `hΦinf`). The conclusion has two parts: first, $y\mapsto \Phi(\mathrm{toSIdele}\,y)$ is injective on [`NumberField.SArchIdele.obj E K S`](def/NumberField_SArchIdeleModule.html#L32), where `toSIdele` is the product lift of the component maps `toSIdeleComponent`; second, for every unit $z$ of $\mathbb A_K$, $z$ lies in the image of this map precisely when $\mathrm{finPart}_w(z)=1$ for every finite place $w$ of $K$ with $w\cap\mathcal O_E\notin S$.
--
--   This identifies the $S\cup\infty$-idèle module, viewed inside the idèle group of $K$ through a given embedding of the larger $S$-idèle module, with the subgroup of idèles whose components are trivial at all finite places not lying above $S$ — the classical group $J_S$ of $S$-idèles. It is used to obtain the unique Galois-equivariant map to the restricted idèle representation in [`NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq`](thm.html#NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff.lean

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

theorem NumberField.SArchIdele.injective_comp_toSIdele_and_mem_range_iff
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
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
          (NumberField.ArchIdele.above E K v).Completion)) :
    Function.Injective (fun y : NumberField.SArchIdele.obj E K S => Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)) ∧
    ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      (∃ y : NumberField.SArchIdele.obj E K S, Φ ((NumberField.SArchIdele.toSIdele E K S).hom y) = Additive.ofMul z) ↔
        ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → finPart w z = 1 := by sorry
