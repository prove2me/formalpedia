-- Prove2me | Theorems.Thm_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
-- name    : M4aHerbrand.exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e4fb0904-649d-55cd-969c-d7afdc9d3d61
-- title:
--   Exactness at H²(G,I_F) for a cyclic layer
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois and with $G = \operatorname{Gal}(F/E)$ cyclic, and let $D$ be a descent datum for the adèles of $F$ over $E$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $G$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_F, F)$, each automorphism continuous and compatible with the structure map $F \to \mathrm{AdeleRing}(\mathcal{O}_F,F)$ in the sense that $D.\mathrm{act}\,g$ applied to the image of $x \in F$ is the image of $g x$. Multiplicative actions of $G$ are assumed on the idèles $(\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times$, on the idèle class group $(\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times / \mathrm{principalIdeles}$ (the quotient by the image of $F^\times$ under the unit map of $F \to \mathrm{AdeleRing}(\mathcal{O}_F,F)$), and on $F^\times$, pinned respectively to the unit automorphism $D.\mathrm{unitsAct}$ induced by $D.\mathrm{act}$, to the induced automorphism $D.\mathrm{classAct}$ of the quotient, and to $a \mapsto g(a)$. Let $j$ be a morphism of $\mathbb{Z}[G]$-representations from $F^\times$ to the idèles whose value on $a$ is the image of $a$ under the unit map of $F \to \mathrm{AdeleRing}(\mathcal{O}_F,F)$, and $\pi$ a morphism from the idèles to the idèle class group given by the quotient map. Then for every $x \in H^2(G, \mathbb{I}_F)$ whose image under the map induced by $\pi$ (along the identity of $G$) vanishes, there is $\alpha \in H^2(G, F^\times)$ whose image under the map induced by $j$ equals $x$.
--
--   This is exactness at $H^2(G,\mathbb{I}_F)$ of the cohomology sequence attached to $1 \to F^\times \to \mathbb{I}_F \to C_F \to 1$ for a cyclic layer $F/E$, i.e. the inclusion $\ker\big(H^2(G,\mathbb{I}_F) \to H^2(G,C_F)\big) \subseteq \operatorname{im}\big(H^2(G,F^\times) \to H^2(G,\mathbb{I}_F)\big)$. It is used to descend the sum of local invariant functionals from $H^2(G,\mathbb{I}_F)$ to $H^2(G,C_F)$, in [`M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic`](thm.html#M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic.lean

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

theorem M4aHerbrand.exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (π : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hπ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
    (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))
    (hx : (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = 0) :
    ∃ α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2), (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α = x := by sorry
