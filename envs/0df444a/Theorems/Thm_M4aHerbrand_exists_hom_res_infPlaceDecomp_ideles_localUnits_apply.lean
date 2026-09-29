-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
-- name    : M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f9c87400-0d4e-5162-84ff-4cf483579208
-- title:
--   Archimedean coordinate maps of the idèle units are decomposition-equivariant
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an extension of $E$, and let $G = \mathrm{Gal}(F/E)$ be written `F ≃ₐ[E] F`. Let $D$ be an idèle Galois descent datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $G$ to the ring automorphisms of $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, each of which is continuous and restricts along $F \to \mathbb{A}_F$ to the given action of $g$ on $F$. Assume further that $G$ acts on the unit group $\mathbb{A}_F^\times$ by multiplicative distributive automorphisms, and that this action agrees with the one induced by $D$, namely $g \cdot x =$ `Units.mapEquiv` of $D.\mathrm{act}\,g$ applied to $x$ for all $g$ and $x$. Then there is a family $\mathrm{prInf}$, indexed by the infinite places $v$ of $F$, of morphisms of $\mathbb{Z}$-linear representations of the decomposition group $\mathrm{decomp}(E,F,v) = \mathrm{Stab}_G(v)$, from the restriction along the inclusion $\mathrm{Stab}_G(v) \hookrightarrow G$ of the additive representation attached to $\mathbb{A}_F^\times$ to the additive representation attached to $(F_v)^\times$ (the units of the completion of $F$ at $v$), such that for every $v$ and every $x \in \mathbb{A}_F^\times$, $\mathrm{prInf}(v)$ sends $x$ to the $v$-component of the unit `infPart x` of the infinite adèle ring obtained from $x$ by the first projection $\mathbb{A}_F = \mathbb{A}_{F,\infty} \times \mathbb{A}_{F,\mathrm{fin}} \to \mathbb{A}_{F,\infty}$.
--
--   This records, at the level of the full Galois group acting on the idèle units, that the archimedean coordinate map $x \mapsto x_v$ is equivariant for the decomposition group at $v$, with its value on each idèle pinned down. It is the archimedean input to the Shapiro-style decomposition of the idèle module into local pieces, and is cited in the construction of local summands and local fundamental classes used in the Herbrand-quotient computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp Pointwise

theorem M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x) :
    ∃ prInf : ∀ v : InfinitePlace F,
        Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          NumberField.InfPlaceDecomp.localUnits E F v,
      ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)) := by sorry
