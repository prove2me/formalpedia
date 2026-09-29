-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0b5854ea-1949-5647-9f57-b71d8f999eb3
-- title:
--   Removing non-identity components of a closed fibre from a group scheme
-- statement:
--   Let $R$ be a commutative ring, $B$ a scheme and $g\colon B\to\operatorname{Spec}R$ a morphism that is locally of finite type and quasi-compact, and let `LB` be a relative group law for $g$ over $R$: a group structure on the set of $T$-points $\{\varphi\colon T\to B\mid \varphi\circ g=t\}$ for every $R$-scheme $(T,t)$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverses, and naturality in $T$ along morphisms $\psi$ with $\psi$ followed by $t$ equal to $t'$. Let $K$ be a field and $\iota\colon\operatorname{Spec}K\to\operatorname{Spec}R$ a closed immersion. Write $p=$ `pullback.fst g ι` for the projection of the fibre $B\times_{\operatorname{Spec}R}\operatorname{Spec}K$ to $B$, let `LB.baseChange ι` be the base-changed relative group law over $K$ for the second projection, and let $e$ be the point of the fibre obtained by evaluating the underlying map of its unit $K$-point at the closed point of $\operatorname{Spec}K$; let $C=\operatorname{connectedComponent}(e)$. Then there exist a scheme $U$, a morphism $i\colon U\to B$ and a relative group law `LU` for $i$ followed by $g$ over $R$ such that: $i$ is an open immersion; the range of $i$ is the complement of $p(C^{\mathsf c})$; the $p$-preimage of the range of $i$ is exactly $C$; the complement of the range of $p$ is contained in the range of $i$; for every $R$-scheme $(T,t)$ and all $T$-points $x,y$ of $U$ over $t$, composing `LU.mul t x y` with $i$ gives `LB.mul t` applied to the composites of $x$ and $y$ with $i$; and if `LB` is commutative then so is `LU`.
--
--   This is the standard construction, used throughout the theory of Néron models, of the open subgroup scheme obtained from a group scheme of finite type over a base by discarding the non-identity connected components of one closed fibre; over a discrete valuation ring, applied to a Néron model, it yields the identity-component subgroup scheme $A^0$. No smoothness, flatness, separatedness or commutativity hypotheses enter. It feeds the passage from Néron-model property bundles to abelian-scheme property bundles, and the construction of a proper smooth model in the work on $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion ι] :
    ∃ (U : Scheme.{u}) (i : U ⟶ B) (LU : RelativeGroupLaw R (i ≫ g)),
      IsOpenImmersion i ∧
      Set.range i =
        (pullback.fst g ι ''
          (connectedComponent
            (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1
              (IsLocalRing.closedPoint K)))ᶜ)ᶜ ∧
      pullback.fst g ι ⁻¹' Set.range i =
        connectedComponent
          (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) ∧
      (Set.range (pullback.fst g ι))ᶜ ⊆ Set.range i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        NeronModelInfra.schemeHomOverComp (LU.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g) =
          LB.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))) ∧
      (LB.IsCommutative → LU.IsCommutative) := by sorry
