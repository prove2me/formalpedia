-- Prove2me | Theorems.Thm_M4aHerbrand_exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic
-- name    : M4aHerbrand.exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/43864297-cfd7-5ba9-95b8-23396db47b04
-- title:
--   Surjectivity of H²(G,I_F)→ H²(G,C_F) for cyclic G
-- statement:
--   Let $E\subseteq F$ be number fields with $F/E$ Galois and $G=\mathrm{Gal}(F/E)$ cyclic, and let $D$ be a datum of type `IdeleGaloisDescent (𝓞 F) E F`, that is, a monoid homomorphism $D.\mathrm{act}$ from $G$ to the ring automorphisms of the adèle ring of $F$ which is compatible with the structure map $F\to\mathbb{A}_F$ (so $D.\mathrm{act}\,g$ restricts to $g$ on $F$) and continuous in each $g$. Assume the multiplicative $G$-action on $\mathbb{A}_F^\times$ is pinned to $D.\mathrm{unitsAct}$ (the automorphisms induced on units) and the $G$-action on the idèle class group $\mathbb{A}_F^\times/\mathrm{principalIdeles}$, the quotient by the image of $F^\times$, is pinned to $D.\mathrm{classAct}$ (the induced automorphisms of that quotient). Let $\pi$ be a morphism of $\mathbb{Z}$-linear $G$-representations from the additive copy of $\mathbb{A}_F^\times$ to the additive copy of the idèle class group whose underlying map sends each idèle $x$ to its class. Then for every $c$ in $H^2(G,\,C_F)$ there is $x$ in $H^2(G,\,\mathbb{A}_F^\times)$ with $(\mathrm{groupCohomology.map}\ \mathrm{id}_G\ \pi\ 2)(x)=c$; that is, the induced map on second cohomology is surjective.
--
--   For a cyclic layer this is the step, in the computation of the Brauer group of a number field, which says that the second cohomology of the idèle class group is a quotient of that of the idèles; classically it follows from $H^3(G,F^\times)\cong H^1(G,F^\times)=0$ via periodicity and Hilbert 90. It feeds the construction of the invariant map of a cyclic layer, and fails for non-cyclic $G$ (already for $G=V_4$).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (π : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hπ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
    (c : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)) :
    ∃ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2), (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = c := by sorry
