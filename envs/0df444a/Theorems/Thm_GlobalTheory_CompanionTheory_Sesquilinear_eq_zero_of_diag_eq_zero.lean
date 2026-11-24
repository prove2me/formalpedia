-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Sesquilinear_eq_zero_of_diag_eq_zero
-- name    : GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:37.559581+00:00
-- url     : https://prove2.me/theorems/6a799802-14e0-4172-b91c-8dce500345df
-- title:
--   Sesquilinear: eq zero of diag eq zero
-- statement:
--   The Sesquilinear construction uses the eq zero of diag eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SesquilinearEqZeroOfDiagZero.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SesquilinearEqZeroOfDiagZero.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Sesquilinear

theorem GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by sorry
