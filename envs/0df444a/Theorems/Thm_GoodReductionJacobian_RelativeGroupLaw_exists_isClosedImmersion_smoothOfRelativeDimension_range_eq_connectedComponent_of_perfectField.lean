-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/4e7e4ad5-cd7f-5510-aa20-9713281bb9b8
-- title:
--   Smooth irreducible identity component over a perfect field
-- statement:
--   Let $k$ be a perfect field, let $G$ be a scheme and let $f\colon G\to\operatorname{Spec} k$ be quasi-compact and locally of finite type, and let $L$ be a relative group law on $f$: for every $k$-scheme $t\colon T\to\operatorname{Spec} k$ a multiplication, unit and inverse on the set $\{\varphi\colon T\to G \mid \varphi\text{ followed by } f = t\}$, satisfying associativity, both unit laws and the left inverse law, and natural in the test scheme in the sense that for $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$ the multiplication commutes with composition by $\psi$. Then there are a scheme $G_0$, a morphism $i\colon G_0\to G$, a relative group law $L_0$ on $i$ followed by $f$, and $n\in\mathbb N$ such that: $i$ is a closed immersion; $G_0$ is an irreducible topological space; $i$ followed by $f$ is smooth of relative dimension $n$ and geometrically irreducible; the range of $i$ is open and equals the connected component of the image of the closed point of $\operatorname{Spec} k$ under the unit section $L.\mathrm{one}$ at the identity of $\operatorname{Spec} k$; the topological Krull dimension of $G_0$ is $n$; for every $t\colon T\to\operatorname{Spec} k$ and all $x,y$ over $t$ for $i$ followed by $f$, post-composing $L_0.\mathrm{mul}\,t\,x\,y$ with $i$ gives $L.\mathrm{mul}$ of the post-composites of $x$ and $y$ with $i$; $L_0$ is commutative whenever $L$ is; and there is a finite set $S$ of $k$-points of $G$ (sections of $f$ over the identity of $\operatorname{Spec} k$) such that every $k$-point $x$ of $G$ equals $L.\mathrm{mul}$ of some $s\in S$ with the image under $i$ of some $k$-point of $G_0$.
--
--   This is the existence of the identity component of the reduced subscheme of a group scheme of finite type over a perfect field: $(G_{\mathrm{red}})^0$ is a smooth geometrically irreducible closed subgroup scheme which is open in $G$, has the same underlying space as the identity component of $G$, has dimension equal to its relative dimension of smoothness, and is of finite index on $k$-points. It is used downstream in the abelian-scheme and Néron-model infrastructure, for instance in the finiteness statement for translations preserving a Riemann form and in arguments reducing a closed condition on a group scheme to its torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)) (n : ℕ),
      IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧ SmoothOfRelativeDimension n (i ≫ f) ∧
      GeometricallyIrreducible (i ≫ f) ∧
      IsOpen (Set.range i) ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      topologicalKrullDim G₀ = n ∧
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
