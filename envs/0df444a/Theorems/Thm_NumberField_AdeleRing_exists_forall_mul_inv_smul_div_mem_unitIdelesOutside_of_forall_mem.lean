-- Prove2me | Theorems.Thm_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
-- name    : NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e28ca3cf-17e6-59d4-b5a4-c5eaab38f267
-- title:
--   Idèle cocycles modulo unit idèles outside S are coboundaries
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, let $G = K \simeq_{\mathrm{alg}[E]} K$ be its Galois group, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. Let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_K$, $E$, $K$, i.e. a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_K$ = `AdeleRing (𝓞 K) K` which is compatible with $\mathrm{alg\,map} : K \to \mathbb{A}_K$ in the sense that $D.\mathrm{act}(g)$ carries the image of $x \in K$ to the image of $g(x)$, and each $D.\mathrm{act}(g)$ is continuous. Assume a multiplicative distributive $G$-action on $\mathbb{A}_K^{\times}$ is given which agrees pointwise with the action induced by $D$ on units. Write $U_S$ for the subgroup `unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}` of $\mathbb{A}_K^{\times}$, consisting of those units whose finite-adelic component $\delta$ satisfies, at every height-one prime $w$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ does not lie in $S$, that both $\delta_w$ and $(\delta^{-1})_w$ lie in the valuation ring of $K_w$. Then for every function $c : G \to \mathbb{A}_K^{\times}$ with $c(g)\,(g \cdot c(h))/c(gh) \in U_S$ for all $g,h \in G$, there exists $q \in \mathbb{A}_K^{\times}$ such that $c(g)\,\bigl((g\cdot q)/q\bigr)^{-1} \in U_S$ for all $g \in G$.
--
--   This is the cochain-level form of the vanishing $H^1(G, \mathbb{I}_K/U_S) = 0$: modulo the unit idèles outside $S$, the quotient of the idèle group is the permutation module $\bigoplus_{w \nmid S} \mathbb{Z}$ on the primes of $K$ not above $S$, and a $1$-cocycle there is a coboundary. It is used in the treatment of $S$-idèle classes, in particular for the uniqueness statement [`NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero`](thm.html#NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero) and for the injectivity of the induced map on $H^2$ in [`NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside`](thm.html#NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory groupCohomology

theorem NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (c : (K ≃ₐ[E] K) → (AdeleRing (𝓞 K) K)ˣ)
    (hc : ∀ g h : K ≃ₐ[E] K, c g * (g • c h) / c (g * h) ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) :
    ∃ q : (AdeleRing (𝓞 K) K)ˣ, ∀ g : K ≃ₐ[E] K,
      c g * (g • q / q)⁻¹ ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by sorry
