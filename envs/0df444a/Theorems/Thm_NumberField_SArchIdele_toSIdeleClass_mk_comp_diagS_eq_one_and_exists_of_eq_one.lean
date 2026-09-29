-- Prove2me | Theorems.Thm_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
-- name    : NumberField.SArchIdele.toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/033ee5bc-9c9c-5879-8aa6-240d8784ded0
-- title:
--   Exactness at the S∪∞-idèle module
-- statement:
--   Let $E$ and $K$ be number fields with $K/E$ Galois, and let $S$ be a finite set of nonzero primes of $\mathcal O_E$. Let $J=$ [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) be the $\mathbb Z[\mathrm{Gal}(K/E)]$-module formed as the product, indexed by the primes $v\in S$, the primes $v\notin S$ and the infinite places $v$ of $E$, of the modules coinduced from the decomposition group at the chosen place above $v$ of, respectively, the units of the completion, the units of the valuation ring of the completion, and the units of the archimedean completion. Let $\Phi\colon J\to$ `Additive` $(\mathbb A_K)^\times$ be an additive homomorphism, where $\mathbb A_K$ is the adèle ring of $K$, subject to: $\Phi$ is injective; its image is the subgroup of those idèle units $\delta$ such that at every finite place $w$ of $K$ not lying under a prime of $S$ both $\delta_w$ and $(\delta^{-1})_w$ lie in the valuation ring; and $\Phi$ matches components place by place, in the sense that for each $v\in S$ (respectively $v\notin S$, respectively $v$ infinite), each place $w$ of $K$ and each $y\in\mathrm{Gal}(K/E)$ with $y\cdot w$ equal to the chosen place [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) (respectively [`NumberField.ArchIdele.above E K v`](def/NumberField_ArchimedeanIdeleModule.html#L155)), the transport of the $w$-component of $\Phi x$ along the isomorphism of completions [`NumberField.PlaceTransport.transport`](def/NumberField_PlaceTransport.html#L105) (respectively [`NumberField.InfinitePlaceTransport.transport`](def/NumberField_InfinitePlaceTransport.html#L32)) determined by $y$ equals the value at $y$ of the $v$-component of $x$. Assume finally that $\Phi$ sends the full diagonal [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) of the $S$-unit module [`NumberField.SUnits.sUnitsRep E K S`](def/NumberField_SUnitsModule.html#L52) to principal idèles: for every $x$, $\Phi(\mathrm{diag}\,x)$ is the image of the $S$-unit underlying $x$ under $K^\times\to(\mathbb A_K)^\times$. Put $T=\{w\mid w$ lies under a prime of $S\}$ and let `toSIdeleClass (𝓞 K) K T` be the map induced by the identity of $(\mathbb A_K)^\times$ from the idèle class group $(\mathbb A_K)^\times/\mathrm{principalIdeles}$ onto $(\mathbb A_K)^\times/$`sClassKernel (𝓞 K) K T`. Then two assertions hold. First, for every $x$ in `sUnitsRep E K S`, the class of $\Phi\bigl(\mathrm{toSIdele}(\mathrm{diagS}\,x)\bigr)$ in that quotient is trivial, where `diagS` is the diagonal of the $S$-units into [`NumberField.SArchIdele.obj E K S`](def/NumberField_SArchIdeleModule.html#L32) (the product of the coinduced local-unit fibres at the primes of $S$ and at the infinite places) and `toSIdele` is the inclusion of the latter into $J$ by zero at the primes outside $S$. Second, conversely, if $y$ in `SArchIdele.obj E K S` is such that the class of $\Phi(\mathrm{toSIdele}\,y)$ is trivial, then $y=\mathrm{diagS}\,x$ for some $x$ in `sUnitsRep E K S`.
--
--   This is exactness in the middle of the sequence $0\to E_{K,S}\to J^S_K\to C_{K,T}$ relating the $S$-units of $K$, the module of idèles supported at the places above $S$ and at infinity, and the $T$-idèle class group: the image of the diagonal is exactly the kernel of the class map. It is used in the cohomological computations [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two) and [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one.lean

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

theorem NumberField.SArchIdele.toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
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
          (NumberField.ArchIdele.above E K v).Completion))
    (hΦdiag : ∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
      Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) :
    (∀ x : NumberField.SUnits.sUnitsRep E K S,
      toSIdeleClass (𝓞 K) K {w | w.under (𝓞 E) ∈ S}
        (QuotientGroup.mk (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom x))))) = 1) ∧
    (∀ y : NumberField.SArchIdele.obj E K S,
      toSIdeleClass (𝓞 K) K {w | w.under (𝓞 E) ∈ S}
        (QuotientGroup.mk (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) = 1 →
      ∃ x : NumberField.SUnits.sUnitsRep E K S, (NumberField.SArchIdele.diagS E K S).hom x = y) := by sorry
