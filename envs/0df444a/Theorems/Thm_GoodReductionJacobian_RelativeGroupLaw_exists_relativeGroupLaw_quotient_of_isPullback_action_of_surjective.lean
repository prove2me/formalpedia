-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/81f7bd33-32a2-576a-9ce6-3317bd326a98
-- title:
--   Group law on a quotient by a closed normal subgroup
-- statement:
--   Let $R$ be a commutative ring, let $f : G \to \operatorname{Spec} R$ be a scheme over $R$ and let $L$ be a relative group law on $f$, that is, a group structure on the set $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of points of $G$ over each $R$-scheme $t : T \to \operatorname{Spec} R$ (operations `mul`, `one`, `inv` with associativity, two-sided unit, left inverse, and naturality of `mul` under precomposition with $R$-morphisms $T' \to T$). Let $i : N \to G$ be a closed immersion and $L_N$ a relative group law on $i \circ f$ such that, for all $T$-points $x, y$ of $N$ over $t$, $i \circ (x \cdot_{L_N} y) = (i \circ x) \cdot_L (i \circ y)$ (so $i$ is a homomorphism), and such that for every $T$-point $x$ of $G$ and every $T$-point $n$ of $N$ there is a $T$-point $n'$ of $N$ with $i \circ n' = (x \cdot_L (i \circ n)) \cdot_L x^{-1}$ (normality). Let $f_Q : Q \to \operatorname{Spec} R$ and let $q : G \to Q$ be a morphism over $\operatorname{Spec} R$ which is flat, locally of finite presentation, surjective and quasi-compact. Assume that the second projection $N \times_{\operatorname{Spec} R} G \to G$ and the translation action $(n,x) \mapsto (i \circ n) \cdot_L x$ (the map `L.action i`) become equal after composition with $q$, that the resulting square with both legs $q$ is a pullback, i.e. $N \times_{\operatorname{Spec} R} G \cong G \times_Q G$, and that $q$ is the coequaliser of these two morphisms. Then there exists a relative group law $L_Q$ on $f_Q$ such that $q \circ (x \cdot_L y) = (q \circ x) \cdot_{L_Q} (q \circ y)$ for all $T$-points $x, y$ of $G$; $L_Q$ is commutative whenever $L$ is; and for a $T$-point $x$ of $G$ one has $q \circ x = (L_Q)_{\mathrm{one}}(t)$ if and only if $x = i \circ y$ for some $T$-point $y$ of $N$. No uniqueness of $L_Q$ is asserted.
--
--   This is the descent of a group law along an effective flat quotient map: the quotient of a relative group scheme by a closed normal subgroup scheme carries a group law for which the projection is a homomorphism with kernel exactly the given subgroup, in the form of group structures on points functorially in the base. It is used in the construction of the quotient in the good-reduction study of Jacobians, being cited by [`GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isPullback_action_of_surjective
    {R : Type u} [CommRing R] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw R (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
            (L.inv t x))
    {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of R)} (q : SchemeHomOver f fQ)
    [Flat q.1] [LocallyOfFinitePresentation q.1] [Surjective q.1] [QuasiCompact q.1]
    (w : CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ q.1 = L.action i ≫ q.1)
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q.1 q.1)
    (hcoeq : IsColimit (Cofork.ofπ q.1 w)) :
    ∃ LQ : RelativeGroupLaw R fQ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q)) ∧
      (L.IsCommutative → LQ.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) := by sorry
