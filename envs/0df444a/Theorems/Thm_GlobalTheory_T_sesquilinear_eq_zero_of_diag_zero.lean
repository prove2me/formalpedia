-- Prove2me | Theorems.Thm_GlobalTheory_T_sesquilinear_eq_zero_of_diag_zero
-- name    : GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:19.522744+00:00
-- url     : https://prove2.me/theorems/3a35e158-0639-4674-8b86-59f05925cd8e
-- title:
--   T: sesquilinear eq zero of diag zero
-- statement:
--   The T construction uses the sesquilinear eq zero of diag zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SesquilinearEqZeroOfDiagZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SesquilinearEqZeroOfDiagZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by sorry
