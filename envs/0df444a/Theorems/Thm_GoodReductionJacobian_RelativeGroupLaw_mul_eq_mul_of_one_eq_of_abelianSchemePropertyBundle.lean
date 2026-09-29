-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/97be15db-ee0b-5b54-8f20-8edfadf86da9
-- title:
--   Rigidity: relative group laws with equal unit agree
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism satisfying `AbelianSchemePropertyBundle R f`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(s)$ (the preimage of $\{s\}$ under the underlying continuous map of $f$) is connected, and there exists at least one relative group law on $f$. Let $L$ and $L'$ be two elements of `RelativeGroupLaw R f`; such a datum assigns to every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to X \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $X$ over $t$, subject to associativity, the two unit laws, the left inverse law, and naturality: pre-composition with any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$ commutes with the multiplication. Assume that the unit sections of $L$ and $L'$ for the identity morphism of $\operatorname{Spec} R$ have the same underlying morphism $\operatorname{Spec} R \to X$. Then for every scheme $S$, every $s \colon S \to \operatorname{Spec} R$ and all $S$-points $x, y$ of $X$ over $s$, the products $L.\mathrm{mul}\,s\,x\,y$ and $L'.\mathrm{mul}\,s\,x\,y$ are equal.
--
--   This is the rigidity statement that a group law on an abelian scheme is determined by its unit section, so that the group structure on $X$ over $\operatorname{Spec} R$ is unique once the origin is fixed. It is used to prove commutativity of such a group law, and in the identification of the group structures on Néron models and Jacobians of modular curves occurring later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (hX : AbelianSchemePropertyBundle R f) (L L' : RelativeGroupLaw R f)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f) :
    L.mul s x y = L'.mul s x y := by sorry
