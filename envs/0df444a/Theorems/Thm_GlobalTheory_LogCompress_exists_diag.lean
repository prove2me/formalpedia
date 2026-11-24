-- Prove2me | Theorems.Thm_GlobalTheory_LogCompress_exists_diag
-- name    : GlobalTheory.LogCompress.exists_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:16:57.392885+00:00
-- url     : https://prove2.me/theorems/74d8ff9e-f88d-4851-b716-50b5b28079ff
-- title:
--   Log Compress: exists diag
-- statement:
--   The Log Compress construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L56-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TraceLogLeLogDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.LogCompress

theorem GlobalTheory.LogCompress.exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by sorry
