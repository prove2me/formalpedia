-- Prove2me | Theorems.Thm_NumberField_SIdele_injective_map_H2_of_injective_of_range_eq_unitIdelesOutside
-- name    : NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/f04ea867-031b-55a5-9cba-5c0dc0e48b39
-- title:
--   Injectivity on H² of the S-idèle inclusion
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for the Galois group, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) datum for $\mathcal{O}_K$, $E$, $K$, that is, a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring $\mathbb{A}_K$ which is compatible with the structure map $K \to \mathbb{A}_K$ and acts continuously, and suppose the ambient multiplicative-distributive action of $G$ on $\mathbb{A}_K^\times$ satisfies $g \cdot x = D.\mathrm{unitsAct}\,g\,x$ for all $g$ and $x$. Let $\Psi$ be a morphism of $\mathbb{Z}[G]$-representations from the $S$-idèle module [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75) — the product, over the index type `Index E S`, of the coinduced representations attached to the decomposition subgroups: local units at the finite places in $S$, local integer units at the finite places outside $S$, and the archimedean local units — to `Rep.ofMulDistribMulAction` on the additive group underlying $\mathbb{A}_K^\times$. Assume $\Psi$ is injective on underlying modules and that its image consists exactly of those $y \in \mathbb{A}_K^\times$ such that for every finite place $w$ of $K$ whose underlying prime of $\mathcal{O}_E$ is not in $S$, both the $w$-component of $y$ and that of $y^{-1}$ lie in the valuation ring of the completion at $w$. Then the map induced by $\Psi$ under the degree-$2$ group cohomology functor with $\mathbb{Z}$ coefficients is injective.
--
--   This is the step asserting that $H^2(G, J_{K,S}) \to H^2(G, \mathbb{I}_K)$ is injective for an $S$-idèle module embedded as the idèles that are units outside the places above $S$; no ramification hypothesis enters. It is used in the level-arithmetic comparison [`NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le`](thm.html#NumberField.LevelArith.map_diag_H2pi_eq_zero_of_map_principalIdele_H2pi_eq_zero_of_le), which transfers vanishing statements between the $S$-idèle and full idèle cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_injective_map_H2_of_injective_of_range_eq_unitIdelesOutside.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory groupCohomology

theorem NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) :
    Function.Injective ((groupCohomology.functor ℤ (K ≃ₐ[E] K) 2).map Ψ).hom := by sorry
