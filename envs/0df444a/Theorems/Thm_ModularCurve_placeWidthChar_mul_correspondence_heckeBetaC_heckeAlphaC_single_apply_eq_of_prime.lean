-- Prove2me | Theorems.Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
-- name    : ModularCurve.placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f9cda06a-3a31-500e-8de5-1cbf03b09697
-- title:
--   Width-weighted symmetry of the two Hecke correspondence orientations
-- statement:
--   Let $M,s,q'$ be natural numbers with $M$ and $s$ nonzero, $s$ prime, $q'$ prime, $s \neq q'$, and neither $q'$ nor $s$ dividing $M$, and let $k$ be an algebraically closed field of characteristic $q'$. Write $F =$ `modularFunctionFieldC k M`, the intermediate field of $k((q))$ generated over $k$ by the $q$-expansions `jqModC k` and `jqNModC k M`, and $R =$ `charLDegeneracyRoof k M s`, generated over $k$ by `jqModC k`, `jqNModC k M`, `jqNModC k s` and `jqNModC k (M*s)`; it is assumed that $R$ has principal divisors over $k$, i.e. every nonzero $f \in R$ has its order function $v \mapsto v.\mathrm{ord}\,f$ realised by a divisor of degree $0$. Let $\alpha =$ `heckeAlphaC k M s` be the inclusion $F \hookrightarrow R$ and $\beta =$ `heckeBetaC k M s` the second degeneracy embedding, both assumed integral as ring maps (`hα`, `hβ`). Then for all places $w_0, w'$ of $F$ over $k$ (valuation subrings containing $k$, proper, with principal ideals),
--   $$\mathrm{w}(w')\,\bigl(\alpha_{*}\beta^{*}[w_0]\bigr)(w') = \mathrm{w}(w_0)\,\bigl(\beta_{*}\alpha^{*}[w']\bigr)(w_0),$$
--   where $[\,\cdot\,]$ denotes the divisor `Finsupp.single · 1`, each correspondence is pullback along the first map followed by pushforward along the second, and $\mathrm{w} =$ `placeWidthChar q' M` is the width invariant of a place, the quotient of `jWidthChar q'` of its value at `jGeomGen k M` by `placeRamificationJ M`.
--
--   This is the divisor-matrix form of the adjointness between the two orientations of the degeneracy (Hecke) correspondence at the prime $s$ on the characteristic-$q'$ modular curve of level $M$, with the coefficients weighted by the widths of the places. It is obtained by summing the place-level cross identity [`ModularCurve.placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime`](thm.html#ModularCurve.placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime) over the roof places lying over $w_0$ and $w'$, the inertia degrees being $1$ since $k$ is algebraically closed, and it is used in the transport of the depth functional and the component-group projections under the Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve
open ModularCurve

theorem ModularCurve.placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors k (charLDegeneracyRoof k M s)]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (w₀ w' : Place k (modularFunctionFieldC k M)) :
    (placeWidthChar q' M w' : ℤ) *
        Divisor.correspondence (heckeBetaC k M s) (heckeAlphaC k M s) hβ hα (Finsupp.single w₀ 1) w' =
      (placeWidthChar q' M w₀ : ℤ) *
        Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single w' 1) w₀ := by sorry
