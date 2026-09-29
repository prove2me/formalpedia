-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.flat_schemeFibreEndo_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/8d75573d-27d9-5a03-8692-0815192bae3f
-- title:
--   Fibrewise flatness of multiplication by n
-- statement:
--   Let $R$ be a noetherian commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$ a morphism. Let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to J \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} R$, given by multiplication, unit and inverse operations satisfying associativity, the two unit laws and left inversion, and compatible with precomposition along any $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Assume `AbelianSchemePropertyBundle R f`: $f$ is smooth, proper, each fibre $f^{-1}(s)$ of the underlying map of spaces is connected, and a relative group law for $f$ exists. Let $n$ be a natural number with $n > 0$, and let $L.\mathrm{schemeNsmul}\ n \colon J \to J$ be the morphism underlying the $n$-fold $L$-sum of the identity point of $J$ over $f$. Assume this morphism is finite, and let $s$ be a point of $\operatorname{Spec} R$. Then the endomorphism of the fibre $J \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(s)$ induced by $L.\mathrm{schemeNsmul}\ n$ (the morphism into the pullback with components the first projection followed by $L.\mathrm{schemeNsmul}\ n$, and the second projection) is flat.
--
--   This is the fibrewise form of flatness of multiplication by $n$ on an abelian scheme: each fibre of $f$ is a smooth proper connected group scheme over the residue field $\kappa(s)$, and finiteness of $[n]$ forces flatness there. It feeds the global statements [`GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite`](thm.html#GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite) and [`GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul`](thm.html#GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul), used for the multiplication-by-$n$ maps on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeFibreEndo_schemeNsmul
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f) (n : ℕ) (hn : 0 < n)
    (hfin : IsFinite (L.schemeNsmul n)) (s : Spec (CommRingCat.of R)) :
    Flat (schemeFibreEndo f (L.schemeNsmul n) (L.schemeNsmul_over n) s) := by sorry
