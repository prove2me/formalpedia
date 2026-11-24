-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LinAlg_exists_GL_lastRow_eq
-- name    : GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:52:04.972802+00:00
-- url     : https://prove2.me/theorems/8f40259e-5ee1-4d7f-be3f-d305ff4aefcf
-- title:
--   Lin Alg: exists GL last Row eq
-- statement:
--   The Lin Alg construction uses the exists GL last Row eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGlLastRowEq.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGlLastRowEq.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGlLastRowEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg

theorem GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by sorry
