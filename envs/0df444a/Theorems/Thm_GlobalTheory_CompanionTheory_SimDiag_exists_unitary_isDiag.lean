-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SimDiag_exists_unitary_isDiag
-- name    : GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:58.636442+00:00
-- url     : https://prove2.me/theorems/12d6930f-cf84-4143-b7c0-980e8f30a88e
-- title:
--   Sim Diag: exists unitary is Diag
-- statement:
--   The Sim Diag construction uses the exists unitary is Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CommutingHermitianSimultaneousDiag.lean#L8-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CommutingHermitianSimultaneousDiag.lean#L8-L61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CommutingHermitianSimultaneousDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SimDiag

theorem GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ A ∈ S, Aᴴ = A) (hC : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by sorry
