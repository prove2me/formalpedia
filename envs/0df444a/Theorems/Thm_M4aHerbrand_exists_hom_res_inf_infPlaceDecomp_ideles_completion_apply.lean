-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply
-- name    : M4aHerbrand.exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3007243e-82a0-5347-9cbf-f2d0ea2374c8
-- title:
--   Archimedean coordinate morphisms on idèle units at infinite places
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra and $F/E$ Galois, write $G = F \simeq_{\mathrm{alg}[E]} F$ for the Galois group, and let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism from $G$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_F, F)$ which is compatible with the structure map from $F$ (each $g$ acting on $\mathrm{algebraMap}$ of $x \in F$ by $g x$) and continuous in each $g$. Assume a multiplicative-distributive action of $G$ on the unit group $(\mathrm{AdeleRing}(\mathcal{O}_F, F))^\times$ which, by hypothesis `hactI`, coincides with the one induced by $D$ through `unitsAct`, i.e. $g \cdot x = (D.\mathrm{act}\,g)^\times x$ for all $g$ and all idèle units $x$; and let $H$ be a subgroup of $G$. The assertion is the existence of a family $\mathrm{prInfH}$, indexed by the infinite places $v$ of $F$, of morphisms of $\mathbb{Z}$-representations of the subgroup $H \sqcap \mathrm{decomp}(E,F,v)$ — where $\mathrm{decomp}(E,F,v)$ is the stabiliser of $v$ in $G$ — from the restriction along $H \sqcap \mathrm{decomp}(E,F,v) \le H \le G$ of the representation on $(\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times$ (written additively) to the restriction along $H \sqcap \mathrm{decomp}(E,F,v) \le \mathrm{decomp}(E,F,v)$ of $\mathrm{localUnits}(E,F,v)$, the representation of the stabiliser on $(F_v)^\times$ for the completion $F_v$ at $v$, such that for every infinite place $v$ and every idèle unit $x$ the underlying map sends $x$ to the $v$-coordinate of the archimedean part of $x$: namely $\mathrm{Units.map}$ of evaluation at $v$ applied to `infPart x`, where `infPart` is $\mathrm{Units.map}$ of the projection of the adèle ring onto its infinite-adèle factor.
--
--   These are the archimedean local coordinate maps on the idèle unit group, the infinite-place counterpart of the maps at finite places; they exhibit the $v$-component of the archimedean part as a morphism of $(H \cap D_v)$-modules. They serve as input to the Shapiro-type decomposition of the cohomology of the idèle module restricted to a subgroup, and are used in the comparison of local contributions over decomposition groups in the Herbrand-quotient computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply.lean

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

theorem M4aHerbrand.exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ prInfH : ∀ v : InfinitePlace F,
        Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.InfPlaceDecomp.decomp E F v ≤ H))
            (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
          Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ NumberField.InfPlaceDecomp.decomp E F v ≤ NumberField.InfPlaceDecomp.decomp E F v))
            (NumberField.InfPlaceDecomp.localUnits E F v),
      ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ),
        (prInfH v).hom (Additive.ofMul x) = Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)) := by sorry
