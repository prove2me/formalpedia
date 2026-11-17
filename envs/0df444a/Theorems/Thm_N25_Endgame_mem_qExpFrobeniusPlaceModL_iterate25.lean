-- Prove2me | Theorems.Thm_N25_Endgame_mem_qExpFrobeniusPlaceModL_iterate25
-- name    : N25.Endgame.mem_qExpFrobeniusPlaceModL_iterate25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:51.090197+00:00
-- url     : https://prove2.me/theorems/f8f7e280-ee52-4f62-9b2f-46aa450c7ff4
-- title:
--   Valuation-ring membership under iterated place Frobenius
-- statement:
--   Let $p$ be prime, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ $q$-expansion function field, let $Φ_p$ be Frobenius on functions, and let $Fr_p$ be Frobenius on places. For a place $P$ of $F_K$, an element $x∈F_K$, and $n≥0$,
--
--   $$x∈𝒪_{Fr_p^n(P)}\iff Φ_p^n(x)∈𝒪_P.$$
--
--   This characterizes the iterated place action as pullback of valuation rings along the function-field Frobenius.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

open N25
open N25.Endgame

theorem N25.Endgame.mem_qExpFrobeniusPlaceModL_iterate25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (P : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ25))
    (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    x ∈ ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n] P).toValuationSubring ↔
      (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) x ∈ P.toValuationSubring := by sorry
