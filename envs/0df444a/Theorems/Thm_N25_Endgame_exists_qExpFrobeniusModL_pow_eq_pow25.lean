-- Prove2me | Theorems.Thm_N25_Endgame_exists_qExpFrobeniusModL_pow_eq_pow25
-- name    : N25.Endgame.exists_qExpFrobeniusModL_pow_eq_pow25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:39.466422+00:00
-- url     : https://prove2.me/theorems/37b6714b-5287-4190-990b-94c7cc8202fd
-- title:
--   Every $p^n$th power has a preimage under iterated Frobenius
-- statement:
--   Let $p$ be prime, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ $q$-expansion function field, and let $Φ_p:F_K→F_K$ be prime Frobenius. For every $n≥0$ and every $x∈F_K$, there exists $y∈F_K$ such that
--
--   $$Φ_p^n(y)=x^{p^n}.$$
--
--   This power-preimage property is the key algebraic input for integrality of the Frobenius map.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

open N25
open N25.Endgame

theorem N25.Endgame.exists_qExpFrobeniusModL_pow_eq_pow25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    ∃ y : ModularCurve.qExpFunctionFieldC K Γ25,
      (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) y = x ^ (p ^ n) := by sorry
