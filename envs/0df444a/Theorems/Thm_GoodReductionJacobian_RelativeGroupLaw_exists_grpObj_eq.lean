-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/3094107d-6350-5662-9389-299451f03d24
-- title:
--   A relative group law comes from a group object
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism of schemes, and let $G$ be a relative group law on $f$, that is: for every scheme $T$ with a morphism $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit element and an inversion on the set $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, subject to associativity of the multiplication, the two unit laws, the identity $\mathrm{inv}(x) \cdot x = 1$, and naturality of the multiplication under precomposition with any $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Then there exists a group-object structure $g$ on the object $\mathrm{Over.mk}\,f$ of the over-category of $\operatorname{Spec} R$, taken with its cartesian monoidal structure (so the tensor product is the fibre product over $\operatorname{Spec} R$ and the unit is $\mathrm{id}$ on $\operatorname{Spec} R$), which induces $G$ on points: for every $t \colon T \to \operatorname{Spec} R$ and all morphisms $a, b \colon \mathrm{Over.mk}\,t \to \mathrm{Over.mk}\,f$ in the over-category, the pair morphism $\mathrm{lift}\,a\,b$ followed by $g.\mathrm{mul}$ has underlying morphism $a \cdot_t b$, the map to the monoidal unit followed by $g.\mathrm{one}$ has underlying morphism the unit of $G$ at $t$, and $a$ followed by $g.\mathrm{inv}$ has underlying morphism $\mathrm{inv}_t(a)$; in each case the underlying morphism is extracted by `overHomToSchemeHomOver`, which sends a morphism of the over-category to its component $T \to A$ together with the identity that it is a morphism over $\operatorname{Spec} R$.
--
--   This is the Yoneda-style transport of a functorial group law on the relative points of $f \colon A \to \operatorname{Spec} R$ into a group-object structure on $f$ in the over-category of $\operatorname{Spec} R$; no representability theorem is involved, since the representing object is $f$ itself. It is the interface used by the Néron-model and good-reduction material, for instance in the statements about closed immersions of finite index into an abelian-scheme property bundle and about torsion in the relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory NeronModelInfra
  GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) := by sorry
