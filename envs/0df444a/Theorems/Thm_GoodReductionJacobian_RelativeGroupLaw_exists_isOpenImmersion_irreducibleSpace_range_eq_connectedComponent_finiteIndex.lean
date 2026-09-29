-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0aac8270-2ff9-54bc-9cf7-424ca2a4fd50
-- title:
--   Identity component of a group scheme over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field, let $G$ be a scheme with a morphism $f \colon G \to \operatorname{Spec} k$ that is locally of finite type and quasi-compact, and let $L$ be a relative group law on $f$, i.e. a rule assigning to every $k$-scheme $T$ with structure morphism $t \colon T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi \colon T \to G \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, both unit laws and the left inverse law, and compatible with precomposition by any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Then there exist a scheme $G_0$, a morphism $i \colon G_0 \to G$ and a relative group law $L_0$ on the composite $i$ followed by $f$ such that: $i$ is both an open immersion and a closed immersion; $G_0$ is an irreducible topological space; the set-theoretic image of $i$ is the connected component, in $G$, of the image of the closed point of $\operatorname{Spec} k$ under the unit $T$-point of $L$ for $T = \operatorname{Spec} k$ with $t = \mathbf{1}$; $i$ is a homomorphism, in the sense that for every $t \colon T \to \operatorname{Spec} k$ and all $T$-points $x, y$ of $i$ followed by $f$, postcomposing $L_0.\mathrm{mul}\,t\,x\,y$ with $i$ gives the $L$-product of the postcompositions of $x$ and $y$ with $i$; if $L$ is commutative then so is $L_0$; and there is a finite set $S$ of $k$-points of $f$ (sections over $\mathbf{1}_{\operatorname{Spec} k}$) such that every $k$-point $x$ of $f$ is the $L$-product of some $s \in S$ with the postcomposition with $i$ of some $k$-point $a$ of $i$ followed by $f$.
--
--   This is the classical theorem on the neutral (identity) component $G^{0}$ of a group scheme of finite type over an algebraically closed field, with no smoothness, reducedness or commutativity assumed: $G^{0}$ is the irreducible component through the identity, it is open and closed, carries the induced group law, and its group of $k$-points has finite index in $G(k)$. It is used in the study of Néron models and of Jacobians with good reduction, where component-group and finite-index arguments reduce statements about $G(k)$ to the connected case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)),
      IsOpenImmersion i ∧ IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by sorry
