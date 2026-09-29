-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pullback_iso_pullback_of_comp_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5c2bad2d-0497-5219-bb09-407fd7b826e3
-- title:
--   Shear isomorphism G×_Q G≅ N×_k G for a quotient homomorphism
-- statement:
--   Let $k$ be a commutative ring, let $f : G \to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L$, i.e. functorial maps assigning to each $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set of $k$-morphisms $T \to G$ over $t$, satisfying associativity, the two unit laws, left inverses, and naturality of the multiplication along base change $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $i : N \to G$ be a closed immersion, and let $fQ : Q \to \operatorname{Spec} k$ be another scheme over $k$ with a relative group law $LQ$. Let $q$ be a morphism $G \to Q$ with $q$ followed by $fQ$ equal to $f$. Assume: (i) for every $k$-scheme $t : T \to \operatorname{Spec} k$ and all $x, y : T \to G$ over $t$, the composite of $L.\mathrm{mul}\,t\,x\,y$ with $q$ equals $LQ.\mathrm{mul}$ applied to the composites of $x$ and of $y$ with $q$ (so $q$ is a homomorphism on $T$-valued points); (ii) for every such $t$ and every $x : T \to G$ over $t$, the composite of $x$ with $q$ is the unit $LQ.\mathrm{one}\,t$ if and only if $x$ factors through $i$, i.e. there is $y : T \to N$ over $i$ followed by $f$ whose composite with $i$ is $x$. Then there exists an isomorphism of schemes $e : G \times_Q G \xrightarrow{\sim} N \times_{\operatorname{Spec} k} G$, where the first pullback is taken along $q$ in both factors and the second along $i$ followed by $f$ and along $f$, such that $e$ followed by the second projection of $N \times_{\operatorname{Spec} k} G$ equals the second projection of $G \times_Q G$.
--
--   This is the torsor, or 'shear', isomorphism attached to a homomorphism $q$ whose kernel on points is the closed subscheme $N$: the two maps $(x,y) \mapsto (xy^{-1}, y)$ and $(n,y) \mapsto (ny, y)$ identify $G \times_Q G$ with $N \times_k G$ over the second factor, with no flatness or normality hypothesis imposed. It is used in the good-reduction-of-Jacobians infrastructure, where [`GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff) transports affineness and closed-immersion properties across such a quotient map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pullback_iso_pullback_of_comp_eq_one_iff.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pullback_iso_pullback_of_comp_eq_one_iff
    (k : Type u) [CommRing k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) :
    ∃ e : pullback q.1 q.1 ≅ pullback (i ≫ f) f, e.hom ≫ pullback.snd (i ≫ f) f = pullback.snd q.1 q.1 := by sorry
