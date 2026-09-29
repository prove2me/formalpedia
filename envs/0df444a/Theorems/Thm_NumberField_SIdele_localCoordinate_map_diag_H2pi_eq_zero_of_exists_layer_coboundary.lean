-- Prove2me | Theorems.Thm_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
-- name    : NumberField.SIdele.localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4449511c-7fb2-549f-8e2b-bffd51ffaba2
-- title:
--   Local coordinate at v vanishes for a layer coboundary
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, $G = K \simeq_{\mathrm{alg}[E]} K$ its Galois group, let $S$ be a finite set of height-one primes of $\mathcal{O}_E$, let $f$ be a $2$-cocycle of the $\mathbb{Z}[G]$-module `SUnits.sUnitsRep E K S` (the submodule of the additive group of $K^\times$ cut out by the $S$-unit condition, with $G$ acting), and let $v \in S$. Assume the following: there exist a number field $K''$ with $E$-algebra and $K$-algebra structures forming a scalar tower and with $K''/E$ Galois, a prime $w''$ of $\mathcal{O}_{K''}$ whose contraction to $\mathcal{O}_K$ is the chosen prime `PlaceAbove.above E K v` of $K$ above $v$, and a function $y$ from the decomposition subgroup $D_{w''} \le \mathrm{Gal}(K''/E)$ to the units of the completion $K''_{w''}$, written additively, such that for all $g, h \in D_{w''}$ the image of $f(g|_K, h|_K)$ under $K^\times \to (K'')^\times \to (K''_{w''})^\times$ equals $g \cdot y(h) - y(gh) + y(g)$; multiplicatively, the pulled-back cocycle is the coboundary of $y$ on $D_{w''}$. Then the following element of $H^2(D_w, (K_w)^\times)$ is zero, where $w$ is the chosen prime of $K$ above $v$ and $D_w \le G$ its decomposition subgroup: take the class $H^2\pi(f)$ in $H^2(G, \mathcal{O}_{K,S}^\times)$, push it along the diagonal map [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) into $H^2$ of the product of coinduced local modules indexed by the places of $E$ (finite places in $S$, finite places outside $S$, and infinite places), project to the coordinate `Sum.inl (Sum.inl v)`, i.e. the factor $\mathrm{Coind}_{D_w}^{G} (K_w)^\times$, and apply Shapiro's isomorphism `groupCohomology.coindIso` in degree $2$.
--
--   This is the local criterion used to kill the $v$-coordinate of an $S$-idèle class: since inflation from $H^2(D_w, K_w^\times)$ to $H^2(D_{w''}, (K''_{w''})^\times)$ is injective, by Hilbert 90 for the completed extension together with the surjectivity of $D_{w''} \to D_w$, splitting the cocycle in a higher layer at a place above $v$ forces the $v$-coordinate to vanish. It feeds the global vanishing statement [`groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax), within the class field theory input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.lean

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory groupCohomology
open scoped NumberField.PlaceDecomp

theorem NumberField.SIdele.localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (f : cocycles₂ (SUnits.sUnitsRep E K S)) (v : {v // v ∈ S})
    (hloc : ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra E K'') (_ : Algebra K K'')
      (_ : IsScalarTower E K K'') (_ : IsGalois E K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 K) w'' = PlaceAbove.above E K v.1)
      (y : PlaceDecomp.decomp E K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp E K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap K K'').toMonoidHom (SUnits.val E K S
              (f (AlgEquiv.restrictNormalHom K (g : K'' ≃ₐ[E] K''),
                  AlgEquiv.restrictNormalHom K (h : K'' ≃ₐ[E] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g) :
    (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) (NumberField.SIdele.diag E K S) 2).hom
        (H2π (SUnits.sUnitsRep E K S) f)) = 0 := by sorry
