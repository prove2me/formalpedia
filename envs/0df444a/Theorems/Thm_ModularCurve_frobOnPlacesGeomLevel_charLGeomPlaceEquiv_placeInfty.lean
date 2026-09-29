-- Prove2me | Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
-- name    : ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2e75a144-af69-5ef1-920d-1bb09547ff02
-- title:
--   Geometric Frobenius fixes the place at infinity
-- statement:
--   Let $k$ be a field, equipped with decidable equality on $k(T)$, let $q$ be a prime and let $k$ have characteristic $q$. Let `data` consist of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ in the outer variable which annihilates the pair $(j(\tau), j(q\tau))$ of $q$-expansions, and let `hKr` assert Kronecker's congruence for it, namely that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ (written with the inner and outer variables as in the definition). Consider the place at infinity of the rational function field $k(T)$, that is the valuation subring of the valuation $\mathrm{inftyValuation}$, viewed as a place of the level-one modular function field $\mathrm{modularFunctionFieldC}\,k\,1 = k(\tilde\jmath, \tilde\jmath)\subseteq k((T))$ by transport along the $k$-algebra isomorphism $k(T) \cong \mathrm{modularFunctionFieldC}\,k\,1$ sending $T$ to the reduced $q$-expansion $\tilde\jmath$. The assertion is that this place is fixed by the geometric Frobenius operation `frobOnPlacesGeomLevel` on places at level one, which sends a place $w$ to the place obtained by restricting $w$ to the image of the modular function field under the $q$-power substitution on Laurent series and transporting the result back along the induced isomorphism onto that image.
--
--   This is the statement that the cusp $\tilde\jmath = \infty$ of the $j$-line in characteristic $q$ is a fixed point of the geometric Frobenius correspondence built from a modular polynomial satisfying Kronecker's congruence. It enters the bookkeeping of cusps in the level-one gluing of place specialisations, where one needs that no place of strict type specialises to a Frobenius-fixed cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
    (k : Type*) [Field k] [DecidableEq (RatFunc k)] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))
      = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by sorry
