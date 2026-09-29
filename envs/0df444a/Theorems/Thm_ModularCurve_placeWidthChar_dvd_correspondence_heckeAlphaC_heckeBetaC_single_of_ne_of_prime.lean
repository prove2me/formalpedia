-- Prove2me | Theorems.Thm_ModularCurve_placeWidthChar_dvd_correspondence_heckeAlphaC_heckeBetaC_single_of_ne_of_prime
-- name    : ModularCurve.placeWidthChar_dvd_correspondence_heckeAlphaC_heckeBetaC_single_of_ne_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/94583e3e-3871-5149-b38f-234657b2b006
-- title:
--   Width divides off-diagonal Hecke correspondence coefficients in characteristic q'
-- statement:
--   Let $M$ and $s$ be non-zero natural numbers with $s$ prime, let $q'$ be a prime, and assume $s \neq q'$, $q' \nmid M$ and $s \nmid M$. Let $k$ be an algebraically closed field of characteristic $q'$, and suppose the intermediate field $\mathrm{charLDegeneracyRoof}\ k\ M\ s = k(j_q, j_{q,M}, j_{q,s}, j_{q,Ms})$ inside the Laurent series field over $k$ has principal divisors, i.e. every non-zero element $f$ is the divisor of some $D$ with $D(v) = v.\mathrm{ord}\,f$ at every place and $\deg D = 0$. Assume the two degeneracy algebra maps from $\mathrm{modularFunctionFieldC}\ k\ M = k(j_q, j_{q,M})$ into this roof, namely the inclusion `heckeAlphaC k M s` and the map `heckeBetaC k M s`, are integral ring homomorphisms (hypotheses `hα`, `hβ`). Let $v \neq t$ be places of $\mathrm{modularFunctionFieldC}\ k\ M$, and suppose $\mathrm{placeWidthChar}\ q'\ M\ t > 0$, that is, the quotient $\mathrm{jWidthChar}\ q'\,(t.\mathrm{evalAt}\,(\mathrm{jGeomGen}\ k\ M)) / \mathrm{placeRamificationJ}\ M\ t$ is non-zero. Then $\mathrm{placeWidthChar}\ q'\ M\ t$, viewed in $\mathbb{Z}$, divides the coefficient at $v$ of the divisor obtained by pulling the divisor $1\cdot t$ back along `heckeAlphaC` and pushing it forward along `heckeBetaC`.
--
--   This is the off-diagonal divisibility law for the matrix of the degeneracy correspondence acting on places of the modular function field in characteristic $q'$, the divisor being the width of the source place $t$ rather than of the place $v$ where the coefficient is read; it is the companion of the weighted symmetry of the same matrix. It feeds the comparison of Hecke actions on component groups and character lattices in the supersingular-level analysis, being cited in the construction of glued specialisations and in the computation of the rank of the Hecke torsion in the ribbon component group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeWidthChar_dvd_correspondence_heckeAlphaC_heckeBetaC_single_of_ne_of_prime.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeWidthChar_dvd_correspondence_heckeAlphaC_heckeBetaC_single_of_ne_of_prime
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (v t : Place k ↥(modularFunctionFieldC k M))
    (hvt : v ≠ t) (ht : 0 < placeWidthChar q' M t) :
    (placeWidthChar q' M t : ℤ)
      ∣ Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single t 1) v := by sorry
