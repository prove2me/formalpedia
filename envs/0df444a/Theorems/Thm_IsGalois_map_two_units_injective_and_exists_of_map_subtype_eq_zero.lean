-- Prove2me | Theorems.Thm_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero
-- name    : IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/4ac29c68-f9af-5d27-8246-8ec5f993e208
-- title:
--   Degree-two inflation–restriction for Galois unit groups
-- statement:
--   Let $E \subseteq L \subseteq M$ be fields, with $M$ an algebra over both $E$ and $L$, $L$ an algebra over $E$, the scalar tower condition, $M/E$ finite and Galois. Suppose the automorphism groups $L \simeq_{\mathrm{alg}[E]} L$ and $M \simeq_{\mathrm{alg}[E]} M$ act multiplicatively and distributively on $L^\times$ and $M^\times$, the actions being given by applying the automorphism to the underlying field element ($hactL$, $hactM$). Let $S$ be a normal subgroup of $M \simeq_{\mathrm{alg}[E]} M$, let $\iota$ be a group isomorphism $(M \simeq_{\mathrm{alg}[E]} M)/S \cong (L \simeq_{\mathrm{alg}[E]} L)$ such that $\mathrm{algebraMap}_{L,M}(\iota(\bar g)(y)) = g(\mathrm{algebraMap}_{L,M}(y))$ for all $g$ and all $y \in L$, and let $i$ be a morphism of representations of $M \simeq_{\mathrm{alg}[E]} M$ from the restriction along $\iota \circ \pi$ of the module $L^\times$ (written additively) to the module $M^\times$, acting on each unit $a$ as the induced map $L^\times \to M^\times$ of $\mathrm{algebraMap}_{L,M}$. Then the map induced on degree-$2$ group cohomology by the pair $(\iota \circ \pi, i)$ is injective, and every class $y \in H^2(M \simeq_{\mathrm{alg}[E]} M, M^\times)$ whose image under the map induced by the inclusion $S \hookrightarrow M \simeq_{\mathrm{alg}[E]} M$ together with the identity of the restricted module vanishes is of the form $\beta \mapsto y$ for some $\beta \in H^2(L \simeq_{\mathrm{alg}[E]} L, L^\times)$.
--
--   This is the inflation–restriction exact sequence $0 \to H^2(\mathrm{Gal}(L/E), L^\times) \to H^2(\mathrm{Gal}(M/E), M^\times) \to H^2(\mathrm{Gal}(M/L), M^\times)$ in degree two, in the form of injectivity of inflation together with exactness at the middle term, phrased for the abstract data of a normal subgroup $S$ with an identification of the quotient with $\mathrm{Aut}_E(L)$ compatible with the action on $L$. It is used in the Herbrand-quotient/descent computations, being cited by [`M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp`](thm.html#M4aHerbrand.exists_map_map_eq_map_map_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y))
    (i : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)
    (hi : ∀ a : Lˣ, i.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :
    Function.Injective (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom ∧
    ∀ y : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ) 2,
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ))) 2).hom y = 0 →
      ∃ β : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2,
        (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom β = y := by sorry
