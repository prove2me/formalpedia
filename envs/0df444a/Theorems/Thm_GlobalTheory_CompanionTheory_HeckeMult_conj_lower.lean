-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_conj_lower
-- name    : GlobalTheory.CompanionTheory.HeckeMult.conj_lower
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:29.607515+00:00
-- url     : https://prove2.me/theorems/f1d471ca-680a-48b4-b242-0f83f9df9be8
-- title:
--   Hecke Mult: conj lower
-- statement:
--   The Hecke Mult construction uses the conj lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L180-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean#L180-L207

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {K : Type} [Field K] [Algebra R K]

theorem GlobalTheory.CompanionTheory.HeckeMult.conj_lower {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (b : Fin n → ℤ)
    (hb : Antitone b) (L : Matrix (Fin n) (Fin n) R) (hL : CongOne I L)
    (hLt : ∀ i j, i < j → L i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      L.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i))
        = Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i)) * V.map (algebraMap R K) := by sorry
