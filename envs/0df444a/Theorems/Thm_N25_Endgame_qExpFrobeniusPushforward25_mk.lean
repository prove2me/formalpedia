-- Prove2me | Theorems.Thm_N25_Endgame_qExpFrobeniusPushforward25_mk
-- name    : N25.Endgame.qExpFrobeniusPushforward25_mk
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:31.520512+00:00
-- url     : https://prove2.me/theorems/93ea256e-38dc-4892-938d-1a06ecc28cbe
-- title:
--   Frobenius on the Picard group is represented by divisor pushforward
-- statement:
--   Let $ℓ$ be prime, let $K$ be an algebraically closed field of characteristic $ℓ$, let $F_K$ be the level-$25$ function field, and let $D$ be a degree-zero divisor on $F_K$. Write $[D]∈Pic^0(F_K)$ for its class, $Fr_*$ for Frobenius pushforward on divisors, and $Fr_{Pic}$ for Frobenius on the degree-zero Picard group. Then
--
--   $$Fr_{Pic}([D])=[Fr_*(D)].$$
--
--   This makes the Picard Frobenius computable from its action on individual places. Formalization note: the pushed divisor is packaged with its preserved degree-zero certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.qExpFrobeniusPushforward25_mk
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (D : AlgebraicCurve.Divisor.degZero (K := K) (F := FBase K)) :
    ModularCurve.qExpFrobeniusPushforwardModL K Γ25 ℓ
        (AlgebraicCurve.Pic0.mk D) =
      AlgebraicCurve.Pic0.mk
        (ModularCurve.qExpFrobeniusDegZeroPushforwardModL K Γ25 ℓ D) := by sorry
