-- Prove2me | Theorems.Thm_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension
-- name    : NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/384b75af-3ff1-5604-abeb-0526750f9a52
-- title:
--   Néron mapping property from local extension of twisted maps
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, and let $g\colon B\to\operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, equipped with a relative group law $LB$, that is, a group structure on the set of $R$-morphisms $T\to B$ for every $R$-scheme $t\colon T\to\operatorname{Spec} R$, natural in $T$ along morphisms over $\operatorname{Spec} R$. Assume the following extension hypothesis: for every scheme $Z$ with smooth quasi-compact structure morphism $z\colon Z\to\operatorname{Spec} R$, every morphism $u_K$ from the generic fibre $Z_K$ to the generic fibre $B_K$ over $\operatorname{Spec} K$, and every point $\eta$ of $Z\times_R B$ lying over the closed point of $R$ which is maximal for specialisation among such points (any $y$ over the closed point with $\eta$ in the closure of $\{y\}$ equals $\eta$), there exist an open $U\subseteq Z\times_R B$ containing $\eta$ and an $R$-morphism $\tau\colon U\to B$ whose restriction to generic fibres is the restriction to $U_K$ of the twisted map $(\zeta,x)\mapsto u_K(\zeta)\cdot x$, the product being taken for the generic fibre group law of $LB$ of $u_K$ after the first projection and of the second projection. Then `NeronModelPropertyBundle R K g` holds: $g$ is smooth, separated, locally of finite type, quasi-compact, and for every scheme $T$ with smooth $t\colon T\to\operatorname{Spec} R$ restriction to the generic fibre is a bijection from $R$-morphisms $T\to B$ onto $K$-morphisms $T_K\to B_K$.
--
--   This is the verification of the Néron mapping property for a smooth separated group scheme over a discrete valuation ring, reduced to the local extension of twisted maps near the generic points of special fibres in the style of Bosch–Lütkebohmert–Raynaud 4.4. It is used to produce a Néron model bundle, together with the identification of its generic fibre, for an abelian scheme over a henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g)
    (htw : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
      (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
        (pullback.snd g (specGenericFibreInclusion R K)))
      (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
        (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
          pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
              (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :
    NeronModelPropertyBundle R K g := by sorry
