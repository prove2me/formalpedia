-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion
-- name    : GoodReductionJacobian.RelativeGroupLaw.action_shear_and_equivalence_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/276202ee-8cb0-5f95-94cf-0dc11e2b25aa
-- title:
--   Closed subgroup action: shear, freeness, equivalence relation
-- statement:
--   Let $R$ be a commutative ring, $G$ a scheme, $f : G \to \operatorname{Spec} R$ a morphism, and $L$ a relative group law on $f$, that is, a group structure on the set $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, natural in $(T,t)$. Let $i : N \to G$ be a closed immersion and $L_N$ a relative group law on $i$ followed by $f$, and assume $i$ is a homomorphism on points: for every $t : T \to \operatorname{Spec} R$ and all $T$-points $x,y$ of $N$ over $t$, the point $(L_N.\mathrm{mul}\,t\,x\,y)$ followed by $i$ equals $L.\mathrm{mul}$ applied to $x$ followed by $i$ and $y$ followed by $i$. Write $s = \mathrm{pullback.snd}$ for the second projection of $P = N \times_{\operatorname{Spec} R} G$ (the pullback of $i$ followed by $f$ along $f$) and let $a = L.\mathrm{action}\ i : P \to G$ be the product, formed with $L$ over the structure morphism $s$ followed by $f$, of the point $\mathrm{pullback.fst}$ followed by $i$ and the point $s$. The conclusion is fourfold: (i) $a$ followed by $f$ equals $s$ followed by $f$; (ii) there is an automorphism $\sigma$ of $P$ with $\sigma$ followed by $s$ equal to $a$ and $\sigma$ followed by $\mathrm{pullback.fst}$ equal to $\mathrm{pullback.fst}$; (iii) $(s,a)$ is jointly monomorphic: any $a',b' : T \to P$ agreeing after composition with $s$ and after composition with $a$ are equal; (iv) for every scheme $T$, the relation on morphisms $T \to G$ given by $x \sim y$ iff some $\varphi : T \to P$ satisfies $\varphi$ followed by $s$ equal to $x$ and $\varphi$ followed by $a$ equal to $y$, is an equivalence relation.
--
--   This is the statement that the action groupoid of a closed subgroup scheme $N \subseteq G$ on $G$ by translation is a free equivalence relation, with the translation map obtained from the projection by the shear automorphism $(n,x) \mapsto (n, i(n)x)$, so that it inherits the properties of a projection. It supplies the input to the construction of the quotient $G/N$ as an fppf quotient, being used in [`GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_action_shear_and_equivalence_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.action_shear_and_equivalence_of_isClosedImmersion
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    L.action i ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ f ∧
    (∃ σ : CategoryTheory.Limits.pullback (i ≫ f) f ≅ CategoryTheory.Limits.pullback (i ≫ f) f,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = L.action i ∧
      σ.hom ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫ f) f) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f),
      a ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = b ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f → a ≫ L.action i = b ≫ L.action i → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ G =>
      ∃ φ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) f, φ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = x ∧ φ ≫ L.action i = y) := by sorry
