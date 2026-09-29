-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/417a5d36-732d-5c21-9633-a641ab662715
-- title:
--   Proper integral k-scheme realising ordered products of rational points
-- statement:
--   Let $k$ be an algebraically closed field, let $G$ be a scheme with a morphism $g : G \to \operatorname{Spec} k$, and let $L$ be a relative group law on $g$: data assigning to every $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set $\{\varphi : T \to G \mid \varphi \circ g = t\}$ of $T$-valued points of $G$ over $k$, satisfying associativity, both unit laws and the left inverse law, and natural in the sense that for $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ commutes with the multiplication. Let $n$ be a natural number and let $C : \mathrm{Fin}\,n \to \mathrm{Scheme}$ be a family with structure morphisms $c_i : C_i \to \operatorname{Spec} k$, each $c_i$ proper and each $C_i$ integral, together with morphisms $\nu_i : C_i \to G$ over $\operatorname{Spec} k$. The assertion is the existence of a scheme $X$, a proper morphism $x : X \to \operatorname{Spec} k$ with $X$ integral, and a morphism $V : X \to G$ over $\operatorname{Spec} k$, such that: for every section $P$ of $x$ (i.e. every $k$-point of $X$) there is a family of sections $y_i$ of the $c_i$ with $P$ followed by $V$ equal to the right-nested $L$-product, over $\mathrm{Fin}\,n$ in order and starting from the unit of the $k$-points of $G$, of the composites $y_i$ followed by $\nu_i$; and conversely every such family $(y_i)$ arises from some section $P$ of $x$ in this way.
--
--   This is the statement that finitely many proper integral $k$-varieties mapping to a scheme with a relative group law can be replaced by a single proper integral $k$-variety over $G$ whose rational points realise exactly the ordered products of their rational points; the intended $X$ is an iterated fibre product of the $C_i$ and $V$ the product of the pulled-back $\nu_i$ in the group of $X$-valued points. It is used in the theory of abelian schemes, in the proof that a morphism agreeing with a prescribed map on the rational points of a supply of curves is induced by a scheme morphism, part of the infrastructure for extending endomorphisms across Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k g)
    {n : ℕ} {C : Fin n → Scheme.{u}} (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
    [∀ i : Fin n, IsProper (c i)] [∀ i : Fin n, IsIntegral (C i)]
    (ν : ∀ i : Fin n, SchemeHomOver (c i) g) :
    ∃ (X : Scheme.{u}) (x : X ⟶ Spec (CommRingCat.of k)) (_ : IsProper x) (_ : IsIntegral X)
      (V : SchemeHomOver x g),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) ∧
      (∀ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) := by sorry
