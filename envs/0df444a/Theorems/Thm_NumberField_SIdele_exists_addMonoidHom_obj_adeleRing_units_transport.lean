-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_transport
-- name    : NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/78af83e3-72f8-5653-89ed-34df1d2afde2
-- title:
--   S-idèle module realised inside the idèle group
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an algebra over $E$ and $K/E$ Galois, and let $S$ be a finite set of height one primes of $\mathcal{O}_E$. Write $J =$ [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) for the $S$-idèle module, i.e. the representation of $\mathrm{Gal}(K/E) = (K \simeq_{\mathrm{alg}[E]} K)$ over $\mathbb{Z}$ obtained by the `RepPi` construction from the family `fibre E K S`: its underlying module is the product of the underlying modules of the family and the Galois action $\rho$ is coordinatewise. The assertion is that there exists an additive monoid homomorphism $\Phi$ from $J$ to $\mathrm{Additive}\,(\mathbb{A}_K^\times)$, where $\mathbb{A}_K$ is `AdeleRing (𝓞 K) K`, equivalently a group homomorphism from $J$ into the idèle group, with four properties. First, $\Phi$ is injective. Second, its range is the subgroup `AdeleRing.unitIdelesOutside` attached to the set of height one primes $w$ of $\mathcal{O}_K$ with $w$ lying under a member of $S$; that is, the image consists exactly of those adelic units $\delta$ such that for every $w$ whose contraction to $\mathcal{O}_E$ does not lie in $S$, the finite component of $\delta$ and of $\delta^{-1}$ at $w$ both lie in the $w$-adic valuation ring. Third, $\Phi$ is equivariant for the transports of completions: for $g \in \mathrm{Gal}(K/E)$, $x \in J$ and height one primes $w, w'$ with $g \cdot w = w'$, the $w'$-coordinate of the finite part of the idèle $\Phi(\rho(g)x)$ equals `PlaceTransport.transport g h` applied to the $w$-coordinate of the finite part of $\Phi(x)$, and the same statement holds for infinite places $w, w'$ of $K$ with $g \cdot w = w'$, for the infinite part of the idèle and the ring isomorphism `InfinitePlaceTransport.transport g h` between the corresponding completions. Fourth, $\Phi$ carries the diagonal map [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) to principal idèles: for every $x$ in [`NumberField.SUnits.sUnitsRep E K S`](def/NumberField_SUnitsModule.html#L52), the subrepresentation of $\mathrm{Additive}\,K^\times$ cut out by `sUnitsSubmodule E K S`, the element $\Phi(\mathrm{diag}(x))$ is the image of the unit [`NumberField.SUnits.val E K S x`](def/NumberField_SUnitsModule.html#L78) of $K$ under the map $K^\times \to \mathbb{A}_K^\times$ induced by the structure morphism $K \to \mathbb{A}_K$.
--
--   This identifies the abstractly constructed $S$-idèle Galois module with the group of idèles of $K$ that are integral units at all finite places not above $S$, in a form that records the Galois action through the transport isomorphisms of local completions and the compatibility of the diagonal with principal idèles. It is the input to [`NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units`](thm.html#NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units), where the same comparison is phrased without the coordinatewise transport data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_transport.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : HeightOneSpectrum (𝓞 K)) (h : g • w = w'),
        ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
          NumberField.PlaceTransport.transport g h (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : InfinitePlace K) (h : g • w = w'),
        ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' =
          NumberField.InfinitePlaceTransport.transport g h (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w)) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (NumberField.SUnits.val E K S x))) := by sorry
