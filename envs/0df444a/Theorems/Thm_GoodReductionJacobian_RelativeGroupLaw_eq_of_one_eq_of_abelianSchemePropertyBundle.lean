-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b7fdefae-e0c7-5de9-845c-7be0cf6ced92
-- title:
--   A relative group law is determined by its unit section
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and write $\mathrm{SchemeHomOver}\ t\ f$ for the set of $T$-points of $A$ over a structure morphism $t : T \to \operatorname{Spec} R$, i.e. the morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$. Assume `AbelianSchemePropertyBundle R f`: $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ of the underlying continuous map is connected (in particular non-empty), and there exists at least one relative group law on $f$. Here a `RelativeGroupLaw` consists of the data, for every $R$-scheme $(T,t)$, of a multiplication on $\mathrm{SchemeHomOver}\ t\ f$, a distinguished point $\mathrm{one}\ t$, and an inversion, subject to associativity, the two unit laws, the left inverse law, and naturality of the multiplication under precomposition with any $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$. The assertion is: if $L$ and $L'$ are two such relative group laws whose units agree at the single point $T = \operatorname{Spec} R$, $t = \mathrm{id}$, i.e. $L.\mathrm{one}(\mathrm{id}) = L'.\mathrm{one}(\mathrm{id})$ as sections of $f$, then $L = L'$, so the multiplications, units and inversions coincide on $T$-points for every $R$-scheme $T$.
--
--   This is the rigidity statement that a group-scheme structure on an abelian scheme is determined by its zero section; it is the uniqueness half of the construction of the group law from a section, and it is used in the representability and framing results for polarised abelian schemes and in the comparison of group laws under base change and pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L L' : RelativeGroupLaw R f)
    (h : L.one (𝟙 (Spec (CommRingCat.of R))) = L'.one (𝟙 (Spec (CommRingCat.of R)))) : L = L' := by sorry
