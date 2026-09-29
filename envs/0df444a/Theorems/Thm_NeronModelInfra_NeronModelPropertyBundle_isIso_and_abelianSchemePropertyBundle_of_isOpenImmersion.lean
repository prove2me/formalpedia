-- Prove2me | Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
-- name    : NeronModelInfra.NeronModelPropertyBundle.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/db481bea-fbe4-5548-ab5b-f4a04dc7bcf7
-- title:
--   Abelian open subscheme of a Néron model is everything
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain) with field $K$ an $R$-algebra that is a fraction field of $R$. Let $B$ and $U$ be schemes with morphisms $g \colon B \to \operatorname{Spec} R$ and $gU \colon U \to \operatorname{Spec} R$. Assume `NeronModelPropertyBundle R K g`, i.e. $g$ is smooth, separated, locally of finite type and quasi-compact, and for every scheme $T$ and every smooth morphism $t \colon T \to \operatorname{Spec} R$ the map `genericFibreRestrict R K g t`, which passes from morphisms over $\operatorname{Spec} R$ to their restrictions over the generic fibre, is bijective. Assume further that the underlying space of the pullback of $g$ along $\operatorname{Spec}$ of $R \to K$ (the generic fibre of $B$) is preconnected. Let $i \colon U \to B$ be an open immersion with $i$ followed by $g$ equal to $gU$, and assume `AbelianSchemePropertyBundle R gU`: $gU$ is smooth and proper, the preimage under $gU$ of each point of $\operatorname{Spec} R$ is connected, and there exists a relative group law on $gU$, that is a functorial group structure on the sets of $T$-points over $\operatorname{Spec} R$, compatible with base change along morphisms of $\operatorname{Spec} R$-schemes. The conclusion is that $i$ is an isomorphism and that $g$ itself satisfies `AbelianSchemePropertyBundle R g`.
--
--   This isolates the final step of the implication (a) $\Rightarrow$ (b) in the Néron–Ogg–Shafarevich criterion: once an open subscheme of a Néron model is known to be an abelian scheme, it is itself a Néron model of the (connected) generic fibre, hence equals the whole model, which is therefore an abelian scheme. It is used in the derivation of the abelian-scheme property of a Néron model from properness of its fibres, via [`GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper`](thm.html#GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.NeronModelPropertyBundle.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g := by sorry
