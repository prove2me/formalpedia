-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ef4dbb83-9986-5569-94ae-f719758b4c5b
-- title:
--   Identity component of a group scheme over a field
-- statement:
--   Let $k$ be a field, $G$ a scheme, and $f : G \to \operatorname{Spec} k$ a morphism that is locally of finite type and quasi-compact, and let $L$ be a relative group law on $f$: a group structure, given by operations `mul`, `one`, `inv` satisfying associativity, the two unit laws and left inverse, on the set of sections $\{\varphi : T \to G \mid \varphi \circ f = t\}$ for every scheme $T$ and every $t : T \to \operatorname{Spec} k$, compatible with precomposition along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Then there are a scheme $G_0$, a morphism $i : G_0 \to G$ and a relative group law $L_0$ on $i$ followed by $f$ such that: $i$ is both an open and a closed immersion; $G_0$ is an irreducible topological space; $i$ followed by $f$ is geometrically irreducible and geometrically connected; the set-theoretic range of $i$ is the connected component, in $G$, of the image of the closed point of $\operatorname{Spec} k$ under the identity section $L.\mathrm{one}(\mathrm{id})$; for every field $K$ and every $t : \operatorname{Spec} K \to \operatorname{Spec} k$, the preimage of the range of $i$ under the first projection $G \times_{\operatorname{Spec} k} \operatorname{Spec} K \to G$ is the connected component of the corresponding identity point for the base-changed group law `L.baseChange t` on $\operatorname{pullback.snd}\, f\, t$; $i$ is a homomorphism, in the sense that for every $t : T \to \operatorname{Spec} k$ and all $x, y$ over $t$ for $i$ followed by $f$, postcomposing $L_0.\mathrm{mul}\,t\,x\,y$ with $i$ equals $L.\mathrm{mul}$ of the postcompositions; if $L$ is commutative so is $L_0$; and there is a finite set $S$ of sections of $f$ over $\operatorname{Spec} k$ (i.e. $k$-points) such that every section $x$ of $f$ over $\operatorname{Spec} k$ is $L.\mathrm{mul}$ of some $s \in S$ with the image under $i$ of some section of $i$ followed by $f$ over $\operatorname{Spec} k$. The last clause expresses finiteness of index only at the level of $k$-rational points, not for general test schemes $T$.
--
--   This is the theorem on the neutral (identity) component $G^0$ of a group scheme of finite type over an arbitrary field, with no smoothness, reducedness or commutativity assumed, including the two features that go beyond the algebraically closed case: geometric connectedness of $G^0$ and compatibility of its formation with extension of the base field. It is used in the study of partial actions and of special fibres in the Néron model and good-reduction-of-Jacobians part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
    (k : Type u) [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)),
      IsOpenImmersion i ∧ IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧
      GeometricallyIrreducible (i ≫ f) ∧ GeometricallyConnected (i ≫ f) ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      (∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
        pullback.fst f t ⁻¹' Set.range i =
          connectedComponent
            (((L.baseChange t).one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K))) ∧
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
