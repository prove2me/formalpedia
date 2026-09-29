-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/70a1c382-7981-5e5b-bbee-eb50af87dbbf
-- title:
--   Reducedness and smoothness from a factorisation of [m]
-- statement:
--   Let $k$ be a perfect field and let $g : G \to \operatorname{Spec} k$ be a morphism of schemes that is locally of finite type. Suppose $G$ carries a relative group law $L$ over $k$, i.e. for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set of $T$-points over $t$, namely the pairs $\varphi : T \to G$ with $\varphi$ followed by $g$ equal to $t$, satisfying associativity, both unit laws and left inverse, with the multiplication natural under precomposition with any $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equal to $t'$. Assume in addition that this multiplication is commutative on $T$-points for every $T$ and every $t$ (hypothesis `hcomm`). Let $m$ be a natural number whose image in $k$ is a unit, and let $[m] =$ `L.schemeNsmul m` be the endomorphism of $G$ obtained as the first component of the $m$-fold $L$-product of the tautological point $\mathrm{id}_G$ over $g$ with itself, defined by recursion from the unit. If $[m]$ factors as $G \to Z \to G$ through some reduced scheme $Z$, then $G$ is reduced and $g$ is smooth.
--
--   This is the standard criterion that a group scheme locally of finite type over a perfect field on which multiplication by an integer invertible in $k$ factors through a reduced scheme (for instance through $G_{\mathrm{red}}$) is itself reduced, and hence, over a field, smooth; here the group structure is given as a commutative functorial group law on points rather than by a multiplication morphism. It is used in the construction of a smooth model in the work on the modular curve $X_1(p)$, via [`ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
    {k : Type u} [Field k] [PerfectField k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    (m : ℕ) (hm : IsUnit (m : k))
    {Z : Scheme.{u}} [IsReduced Z] (h : G ⟶ Z) (ι : Z ⟶ G)
    (hfac : h ≫ ι = L.schemeNsmul m) :
    IsReduced G ∧ Smooth g := by sorry
