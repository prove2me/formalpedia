-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_semidefinite_null_radical
-- name    : GlobalTheory.T.hermitian_semidefinite_null_radical
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:30.233009+00:00
-- url     : https://prove2.me/theorems/a67e010a-6723-490f-a751-ba8670b40f46
-- title:
--   T: hermitian semidefinite null radical
-- statement:
--   The T construction uses the hermitian semidefinite null radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSemidefiniteNullRadicalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSemidefiniteNullRadicalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadical
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadicalStatement
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

theorem GlobalTheory.T.hermitian_semidefinite_null_radical : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ x, (B x x).re = 0 → ∀ w, B x w = 0 := by sorry
