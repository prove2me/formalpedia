-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset
-- name    : GoodReductionJacobian.RelativeGroupLaw.translate_comp_schemeNsmul_of_mem_torsionSubset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/1995b404-d3c6-5e6d-9cce-5351c52482ec
-- title:
--   Translation by an n-torsion section commutes with [n]
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ be a morphism. Let $L$ be a relative group law on $f$, that is, a choice, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$, of a multiplication, a unit and an inversion on the set $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the unit laws and left inverses, and compatible with precomposition by morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume `L.IsCommutative`, i.e. each of these multiplications is commutative. Let $n$ be a natural number and let $x$ be an element of $\mathrm{SchemeHomOver}\ (\mathbb{1}_{\operatorname{Spec} R})\ f$, i.e. a section of $f$, lying in `L.torsionSubset` for $n$: the $n$-fold iterate `L.nsmul` of the multiplication applied to $x$, starting from the unit, equals the unit section. Write $T_x$ for `L.translate x`, the endomorphism of $A$ obtained as the first component of the product of the identity point $\mathbb{1}_A$ with the point $f$ followed by $x$, and $[n]$ for `L.schemeNsmul n`, the first component of the $n$-fold power of the identity point. The conclusion is that $T_x$ followed by $[n]$ equals $[n]$.
--
--   This is the scheme-theoretic form of the classical identity $[n] \circ T_x = [n]$ for an $n$-torsion section $x$ of a commutative group scheme, formulated for the project's notion of a relative group law on $f : A \to \operatorname{Spec} R$. It is used in the treatment of polarisations and two-torsion characters, where translates of a line bundle by $2$-torsion sections are compared after pullback along $[2]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.translate_comp_schemeNsmul_of_mem_torsionSubset
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n) :
    L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n := by sorry
