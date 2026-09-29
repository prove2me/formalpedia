-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/00cb097f-54ea-53d5-b790-cc2c1b60be87
-- title:
--   Rigidity: fixing the unit section and all geometric points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism satisfying `AbelianSchemePropertyBundle R f`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(s)$ (preimage under the underlying map of $f$) is connected and non-empty, and $f$ admits at least one relative group law. Let $L$ be such a relative group law: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ it equips the set of pairs $(\varphi : T \to A,\ \varphi \circ f = t)$ with multiplication, unit and inverse satisfying associativity, the two unit laws and left inversion, the multiplication being natural in $(T,t)$ along any $\psi : T' \to T$ with $t \circ \psi$ ($\psi$ followed by $t$) equal to $t'$. Let $e : A \to A$ be an endomorphism over the base, $e$ followed by $f$ equal to $f$, such that the unit section $\varepsilon = (L.\mathrm{one}\ \mathrm{id}_{\operatorname{Spec} R}).1 : \operatorname{Spec} R \to A$ satisfies $e \circ \varepsilon = \varepsilon$, and such that for every algebraically closed field $k$ and every morphism $x : \operatorname{Spec} k \to A$ (no compatibility with $f$ required) one has $e \circ x = x$. Then $e = \mathrm{id}_A$. No hypothesis that $e$ be compatible with the group law is imposed.
--
--   This is the rigidity statement for abelian schemes over an arbitrary affine base: an endomorphism of the total space over the base which fixes the unit section and every geometric point is the identity. It is used to prove uniqueness statements for morphisms of abelian schemes, in particular that an endomorphism agreeing with another on geometric points and on the unit section agrees with it, and for the rigidity of level structures on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (e : A ⟶ A) (he : e ≫ f = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ e = (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (hfix : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A), x ≫ e = x) :
    e = 𝟙 A := by sorry
