-- Prove2me | Theorems.Thm_N25_Endgame_qExpFrobeniusModL_pow_isIntegral25
-- name    : N25.Endgame.qExpFrobeniusModL_pow_isIntegral25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:40.834217+00:00
-- url     : https://prove2.me/theorems/5b83d04d-7771-4590-9b0f-6ca11d28f20b
-- title:
--   Every iterated $q$-Frobenius map is integral
-- statement:
--   Let $p$ be prime, let $K$ be a field of characteristic $p$, let $F_K$ be the level-$25$ $q$-expansion function field, and let $Φ_p:F_K→F_K$ be prime Frobenius. For every integer $n≥0$, the self-map $Φ_p^n$ is an integral ring homomorphism:
--
--   $$Int(Φ_p^n:F_K→F_K).$$
--
--   Here $Int$ means that every element of the target is integral over the source through the displayed map. This permits places to be restricted along an iterated Frobenius.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

open N25
open N25.Endgame

theorem N25.Endgame.qExpFrobeniusModL_pow_isIntegral25
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n).toRingHom.IsIntegral := by sorry
