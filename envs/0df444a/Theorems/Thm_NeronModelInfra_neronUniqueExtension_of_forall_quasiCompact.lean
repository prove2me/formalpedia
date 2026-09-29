-- Prove2me | Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
-- name    : NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/aa4c46f4-026d-5857-8e2e-bf5b61f1f15a
-- title:
--   Néron mapping property from the quasi-compact case
-- statement:
--   Let $R$ be a commutative domain and $K$ a field equipped with an $R$-algebra structure making it the fraction field of $R$ (via `IsFractionRing`), and write $\operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism `specGenericFibreInclusion` obtained by applying $\operatorname{Spec}$ to $R \to K$. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a separated morphism. For a scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$, `genericFibreRestrict` is the map sending a morphism $\varphi : T \to X$ with $\varphi$ followed by $f$ equal to $t$ to the morphism of generic fibres $T \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ induced by $\varphi$ on the first factor and the identity on $\operatorname{Spec} K$, regarded as a morphism over $\operatorname{Spec} K$. The hypothesis is that for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} R$ that is both smooth and quasi-compact, this restriction map is bijective. The conclusion is `NeronUniqueExtension R K f`: for every scheme $T$ and every smooth morphism $t : T \to \operatorname{Spec} R$, with no quasi-compactness assumed, the restriction map on $R$-morphisms $T \to X$ is bijective.
--
--   This is the statement that the Néron mapping property for $X/R$ is local on the test scheme, so that it suffices to verify the bijectivity of generic-fibre restriction on quasi-compact (for instance affine) smooth test schemes. It is used to assemble the Néron model property bundle from local or Henselian criteria, being cited by [`NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle`](thm.html#NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle), [`NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension`](thm.html#NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension) and [`NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian`](thm.html#NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t → QuasiCompact t →
      Function.Bijective (genericFibreRestrict R K f t)) :
    NeronUniqueExtension R K f := by sorry
