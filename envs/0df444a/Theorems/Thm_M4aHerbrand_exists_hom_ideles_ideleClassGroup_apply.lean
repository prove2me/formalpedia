-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
-- name    : M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f522e2c3-fe0a-525f-b2ab-d1b020944902
-- title:
--   Equivariance of the idèle class quotient map
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra, and suppose $F/E$ is Galois. Let $D$ be a datum of type `IdeleGaloisDescent (𝓞 F) E F`, that is: a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ of $F$ over $\mathcal{O}_F$, such that each $D.\mathrm{act}\,g$ is continuous and commutes with the structure map $F \to \mathbb{A}_F$ in the sense that it sends the image of $x \in F$ to the image of $g x$. Assume the group $F \simeq_{\mathrm{alg}[E]} F$ acts multiplicatively and distributively on $\mathbb{A}_F^\times$ and on the idèle class group $\mathbb{A}_F^\times / \mathrm{principalIdeles}$ (the quotient by the image of $F^\times$ under the structure map), and that these actions are pointwise given by $D.\mathrm{unitsAct}$ and $D.\mathrm{classAct}$ respectively, i.e. by functoriality of units and the induced map on the quotient. Then there exists a morphism $\pi$ of representations from `Rep.ofMulDistribMulAction` on $\mathbb{A}_F^\times$ to the one on the idèle class group whose underlying additive map sends $x$ (viewed additively) to the class of $x$ (viewed additively).
--
--   This records that the canonical projection from idèles to idèle classes is a map of $\mathrm{Gal}(F/E)$-modules, with its values pinned down on the nose so that later computations may rewrite with it. It is a bookkeeping step in the Sylow-type descent of Tate's reciprocity law from layers with $p$-group Galois group to an arbitrary finite Galois layer, and is cited by the statements about invariant classes and about the vanishing criterion for the image under $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply.lean

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

theorem M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (hact : ∀ (g : F ≃ₐ[E] F) (c : (IdeleClassGroup (𝓞 F) F)), g • c = D.classAct g c) :
    ∃ π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F),
      ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 F) F)) := by sorry
