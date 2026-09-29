-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/1f6e8d37-189f-567e-ada9-e405935c2435
-- title:
--   Multiplication by n on an abelian scheme is locally quasi-finite
-- statement:
--   Let $R$ be a noetherian commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$ a morphism. Let $L$ be a relative group law for $f$: for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} R$ it equips the set of $T$-points $\{\varphi : T \to J \mid \varphi \text{ followed by } f = t\}$ with a multiplication, a unit and an inversion satisfying associativity, both unit laws and the left inverse law, the multiplication being natural in the base: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, composition with $\psi$ is multiplicative. Assume further the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth, proper, that the fibre $f^{-1}(s)$ of the underlying map of spaces over each point $s$ of $\operatorname{Spec} R$ is connected, and that a relative group law for $f$ exists; assume that the multiplication of $L$ is commutative on $T$-points for all $T$ and $t$; and let $n$ be a natural number with $n > 0$. Then the endomorphism $L.\mathtt{schemeNsmul}\ n$ of $J$ — the morphism underlying the $n$-fold product, in the group law on $J$-points over $f$, of the identity point $\mathbf{1}_J$ with itself (defined by recursion: the unit for $n = 0$, and the previous value times the point for each successor) — is locally quasi-finite.
--
--   This is the scheme-theoretic statement that multiplication by $n$ on an abelian scheme has isolated points in its fibres, the first half of the assertion that $[n]$ is an isogeny. It feeds the finiteness and flatness of $[n]$ in [`GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul), used in the treatment of the good-reduction Jacobian and its torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : 0 < n) :
    LocallyQuasiFinite (L.schemeNsmul n) := by sorry
