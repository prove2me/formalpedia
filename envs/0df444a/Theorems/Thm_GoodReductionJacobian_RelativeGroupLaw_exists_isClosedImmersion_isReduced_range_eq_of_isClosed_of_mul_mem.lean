-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c0bfe94f-fae5-56e5-b49e-398528187f47
-- title:
--   Closed submonoid of k-points carries a reduced closed subgroup structure
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes that is locally of finite type and quasi-compact, equipped with a relative group law $L$ over $k$: functorially in a $k$-scheme $t \colon T \to \operatorname{Spec} k$, a multiplication, unit and inverse on the set of $T$-points $\{\varphi \colon T \to G \mid \varphi \circ f = t\}$ satisfying associativity, the two unit laws and left inverses, with multiplication compatible with base change along any $\psi \colon T' \to T$ over $\operatorname{Spec} k$. Let $Z \subseteq G$ be a closed subset of the underlying topological space such that the image of the closed point under the unit point $L.one$ at $t = \mathrm{id}_{\operatorname{Spec} k}$ lies in $Z$, and such that for all $k$-points $x, y$ of $G$ (points over $\mathrm{id}_{\operatorname{Spec} k}$) whose images of the closed point lie in $Z$, the image of the closed point under $L.mul$ of $x$ and $y$ again lies in $Z$. Then there exist a scheme $H$, a morphism $i \colon H \to G$ and a relative group law $LH$ over $k$ on the composite $i$ followed by $f$ such that $i$ is a closed immersion, $H$ is reduced, the set-theoretic range of $i$ is exactly $Z$, and $i$ is a homomorphism on points: for every scheme $T$, every $t \colon T \to \operatorname{Spec} k$ and all $T$-points $x, y$ of $H$ over $t$, composing $LH.mul\,t\,x\,y$ with $i$ equals $L.mul\,t$ applied to the composites of $x$ and of $y$ with $i$.
--
--   This is the classical statement that a closed subset of an algebraic group over an algebraically closed field which contains the identity and is stable under multiplication of its rational points is the underlying set of a reduced closed subgroup scheme, the passage from submonoid to subgroup being automatic. It is used in the study of Néron models and good reduction of Jacobians, for instance to produce proper closed subgroup schemes from partial actions, to propagate a closed condition from torsion points to the whole abelian scheme, and in the finiteness statement for translations preserving a given Riemann form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (Z : Set ↥G) (hZ : IsClosed Z)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ Z)
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1 (IsLocalRing.closedPoint k) ∈ Z → y.1 (IsLocalRing.closedPoint k) ∈ Z →
        (L.mul (𝟙 (Spec (CommRingCat.of k))) x y).1 (IsLocalRing.closedPoint k) ∈ Z) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ IsReduced H ∧ Set.range i = Z ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) := by sorry
