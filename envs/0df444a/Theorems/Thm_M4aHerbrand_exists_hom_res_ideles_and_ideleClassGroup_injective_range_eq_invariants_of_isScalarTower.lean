-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
-- name    : M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/da3012ad-cd55-5103-94ce-cf955d7855a8
-- title:
--   Equivariant idèle base change and Hilbert 90 for idèle classes
-- statement:
--   Let $E$, $F$, $M$ be number fields with $E$-algebra structures on $F$ and $M$, an $F$-algebra structure on $M$ forming a scalar tower over $E$, and with $F/E$ and $M/E$ Galois. Let $D$ and $DM$ be idèle Galois descent data for $F/E$ and $M/E$: for $D$, a monoid homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of $\mathbb{A}_F$ which is compatible with $F \to \mathbb{A}_F$ and continuous in each component, and similarly for $M$. Assume the ambient multiplicative-distributive actions of $F \simeq_{\mathrm{alg}[E]} F$ on $\mathbb{A}_F^{\times}$ and on $C_F = \mathbb{A}_F^{\times}/\operatorname{im}(F^{\times})$ are given by `D.unitsAct` and `D.classAct`, and likewise for $M$ and $DM$. Let $S$ be a normal subgroup of $M \simeq_{\mathrm{alg}[E]} M$ and $\iota$ a group isomorphism $(M \simeq_{\mathrm{alg}[E]} M)/S \cong (F \simeq_{\mathrm{alg}[E]} F)$ such that $\iota(\bar g)$ is the restriction of $g$ to $F$, i.e. $\iota(\bar g)(x)$ and $g(x)$ agree in $M$ for all $x \in F$. The assertion is the existence of morphisms $J$ and $j$ of representations of $M \simeq_{\mathrm{alg}[E]} M$, from the restriction along $\iota \circ (\text{quotient by } S)$ of $\mathbb{A}_F^{\times}$ resp. $C_F$ to $\mathbb{A}_M^{\times}$ resp. $C_M$, such that $J$ is induced on units by the canonical ring homomorphism $\beta \colon \mathbb{A}_F \to \mathbb{A}_M$ of `genuineBaseChange F M`, $j$ sends the class of $x$ to the class of $\beta(x)$, $j$ is injective, and the range of $j$ consists exactly of the classes $c \in C_M$ with $s \cdot c = c$ for all $s \in S$.
--
--   This packages Hilbert's Theorem 90 for idèle classes along $M/F$ — injectivity of $C_F \to C_M$ with image the $\mathrm{Gal}(M/F)$-invariants — together with the Galois equivariance of adelic base change, in the form of morphisms of Galois representations, so that inflation $H^2(\mathrm{Gal}(F/E), C_F) \to H^2(\mathrm{Gal}(M/E), C_M)$ becomes the functorial map along $(\iota \circ \mathrm{pr}, j)$. It is used in the construction and comparison of invariant cohomology classes for idèle class groups, notably in the treatment of fundamental classes and of the $p$-group reduction steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand

theorem M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)]
    (hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c)

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x)) :
    ∃ (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
      (j : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)),

      (∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x)) ∧
      (∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
        Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x) : IdeleClassGroup (𝓞 M) M)) ∧

      Function.Injective j.hom ∧
      (∀ c : IdeleClassGroup (𝓞 M) M,
        Additive.ofMul c ∈ Set.range j.hom ↔ ∀ s : M ≃ₐ[E] M, s ∈ S → s • c = c) := by sorry
