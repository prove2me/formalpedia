-- Prove2me | Theorems.Thm_N25_Endgame_restrictAlong_qExpFrobeniusModL_pow25
-- name    : N25.Endgame.restrictAlong_qExpFrobeniusModL_pow25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:17.014003+00:00
-- url     : https://prove2.me/theorems/9c392226-afb7-4875-b32c-73bb20a1bd79
-- title:
--   Restriction along function Frobenius equals iterated place Frobenius
-- statement:
--   Let $p$ be prime, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ $q$-expansion function field, let $Φ_p$ be Frobenius on $F_K$, and let $Fr_p$ be Frobenius on its places. Since $Φ_p^n$ is integral, restriction of places along it is defined, and for every $n≥0$,
--
--   $$Res_{Φ_p^n}=Fr_p^n.$$
--
--   This identifies the abstract restriction-of-places construction with the concrete Frobenius iterate used in point counting.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_N25_Endgame_qExpFrobeniusModL_pow_isIntegral25

open N25
open N25.Endgame

theorem N25.Endgame.restrictAlong_qExpFrobeniusModL_pow25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    AlgebraicCurve.Place.restrictAlong (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n)
      (qExpFrobeniusModL_pow_isIntegral25 p K n) =
        (ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n] := by sorry
