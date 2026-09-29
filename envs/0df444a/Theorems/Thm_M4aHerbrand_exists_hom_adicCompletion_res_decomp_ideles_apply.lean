-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_adicCompletion_res_decomp_ideles_apply
-- name    : M4aHerbrand.exists_hom_adicCompletion_res_decomp_ideles_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/b8ed0962-b975-5795-81d4-852c1c826d6b
-- title:
--   Equivariance of the concentrated-idèle embedding at a finite place
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and let $D$ be a Galois descent datum for the adèle ring of $F$ over $\mathcal{O}_F$, i.e. a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $\mathrm{Gal}(F/E)$ to the ring automorphisms of $\mathbb{A}_F$ whose value on $\mathrm{algebraMap}$ images of $x \in F$ is the image of $g x$, each automorphism being continuous. Suppose $\mathrm{Gal}(F/E)$ acts multiplicatively on the unit group $\mathbb{A}_F^\times$ and that this action agrees with the one induced by $D$ through `Units.mapEquiv`, that is $g \bullet x = (D.\mathrm{unitsAct}\,g)\,x$ for all $g$ and $x$. Let $\iota$ assign to every finite place $w$ of $F$ (a height-one prime of $\mathcal{O}_F$) a monoid homomorphism $\iota_w \colon (F_w)^\times \to \mathbb{A}_F^\times$ such that for each $x$ the $w$-component of $\iota_w(x)$ (projection of the finite part, `finPart w`) is $x$, the $w'$-component is $1$ for every $w' \neq w$, and the archimedean part `infPart` of $\iota_w(x)$ is $1$. Then there is a family $\iota^D$ of morphisms of representations of the decomposition subgroup $\mathrm{decomp}\,E\,F\,w \le \mathrm{Gal}(F/E)$ (the decomposition subgroup of the valuation subring of $w$) from the multiplicative group $(F_w)^\times$, viewed additively, to the restriction along the inclusion of that subgroup of the representation $\mathbb{A}_F^\times$, whose underlying map sends $\mathrm{Additive.ofMul}\,x$ to $\mathrm{Additive.ofMul}\,(\iota_w x)$ for all $w$ and $x$.
--
--   This is the statement that the concentrated-idèle embedding $F_w^\times \to \mathbb{A}_F^\times$ at a finite place $w$, which places $x$ in the $w$-coordinate and $1$ everywhere else, commutes with the action of the decomposition group at $w$, and so is a morphism of $\mathrm{decomp}\,E\,F\,w$-modules. It serves to transport local cohomology classes at $w$, such as the local fundamental class, into the cohomology of the idèle group and thence of the idèle class group, and is used in the computations of invariants of local fundamental classes and of the continuous cohomology groups attached to the idèle class module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_adicCompletion_res_decomp_ideles_apply.lean

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

theorem M4aHerbrand.exists_hom_adicCompletion_res_decomp_ideles_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1) :
    ∃ ιD : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ),
      ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ), (ιD w).hom (Additive.ofMul x) = Additive.ofMul (ι w x) := by sorry
