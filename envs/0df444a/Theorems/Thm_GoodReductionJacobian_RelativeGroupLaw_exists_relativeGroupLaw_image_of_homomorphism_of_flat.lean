-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_of_flat
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/27e1dba4-5d25-5110-8390-5af556b9cfe4
-- title:
--   Relative group law on the scheme-theoretic image of a homomorphism
-- statement:
--   Let $R$ be a commutative ring. Throughout, a `RelativeGroupLaw R h` for a morphism $h \colon A \to \operatorname{Spec} R$ is the data, for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} R$, of a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \text{ followed by } h = t\}$, subject to associativity, two-sided unit, left inverse, and naturality: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ is multiplicative. Given such a law $L$ on $f \colon J \to \operatorname{Spec} R$ and such a law $L_X$ on a flat $g \colon X \to \operatorname{Spec} R$, let $\sigma$ be a morphism $X \to J$ with $\sigma$ followed by $f$ equal to $g$, assume $\sigma$ quasi-compact and assume that the composite of the scheme-theoretic image inclusion `σ.1.imageι` with $f$ is flat, and assume $\sigma$ is a homomorphism on points: for all $T$, $t$ and all $T$-points $x,y$ of $X$ over $t$, the composite of $L_X(x,y)$ with $\sigma$ equals $L$ applied to the composites of $x$ and of $y$ with $\sigma$. Then there is a relative group law $L_B$ on the structure morphism of the scheme-theoretic image of $\sigma$ over $\operatorname{Spec} R$ such that the image inclusion, viewed as a point of $J$ over that structure morphism, is a homomorphism in the same sense, and such that $L_B$ is commutative on all $T$-points as soon as $L$ is.
--
--   This is the statement that the scheme-theoretic image of a homomorphism of group schemes, flat source and flat image over the base, is a subgroup scheme, expressed in terms of group laws on $T$-points. It is used in the Néron-model infrastructure for the Jacobian of a curve with good reduction, in the variant where the image is proper over the base and in a criterion for a monomorphic homomorphism to be a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_of_flat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_of_flat
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R)} [Flat g] (LX : RelativeGroupLaw R g) (σ : SchemeHomOver g f)
    [QuasiCompact σ.1] [Flat (σ.1.imageι ≫ f)]
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw R (σ.1.imageι ≫ f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
          LB.mul t x y = LB.mul t y x) := by sorry
