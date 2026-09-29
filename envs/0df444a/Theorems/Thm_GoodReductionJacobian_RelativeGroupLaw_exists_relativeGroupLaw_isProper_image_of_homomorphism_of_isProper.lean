-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/06f4e26d-e3d2-5c80-9b8f-aa0d9e43354e
-- title:
--   Proper group law on the image of a homomorphism
-- statement:
--   Let $k$ be a field, let $f : J \to \operatorname{Spec} k$ be separated and locally of finite type, and let $L$ be a relative group law on $f$, i.e. a functorial assignment, to each $k$-scheme $t : T \to \operatorname{Spec} k$, of a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to J \mid \varphi \circ f = t\}$ satisfying associativity, the two unit laws and left inverses, and compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Let $g : X \to \operatorname{Spec} k$ be proper, $L_X$ a relative group law on $g$, and $\sigma$ a morphism $X \to J$ with $\sigma \circ f = g$ which is a homomorphism, in the sense that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and all $T$-points $x, y$ of $X$ over $t$ one has $L_X.\mathrm{mul}\,t\,x\,y$ followed by $\sigma$ equal to $L.\mathrm{mul}$ applied to $x$ followed by $\sigma$ and $y$ followed by $\sigma$. Then there is a relative group law $L_B$ on the structure morphism $\operatorname{im}\sigma \to \operatorname{Spec} k$ obtained as `σ.1.imageι` followed by $f$, such that this structure morphism is proper; the canonical morphism $\operatorname{im}\sigma \to J$ is a homomorphism from $L_B$ to $L$ on $T$-points in the same sense; and if $L$ is commutative on all $T$-points, so is $L_B$.
--
--   This is the statement that the scheme-theoretic image of a proper $k$-group scheme under a homomorphism into a separated $k$-group scheme locally of finite type is a proper closed subgroup scheme, here in the $T$-points formulation of relative group laws. It is used in the construction of the norm-free part attached to the two-chart model of the modular curve $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
    {k : Type u} [Field k]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} [IsSeparated f] [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (LX : RelativeGroupLaw k g) (σ : SchemeHomOver g f)
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw k (σ.1.imageι ≫ f),
      IsProper (σ.1.imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
          LB.mul t x y = LB.mul t y x) := by sorry
