-- Prove2me | Theorems.Thm_GlobalTheory_LogCompress_compress_diag
-- name    : GlobalTheory.LogCompress.compress_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:16:50.456395+00:00
-- url     : https://prove2.me/theorems/c1f40b60-8442-4616-a3a0-3c2d250bcb18
-- title:
--   Log Compress: compress diag
-- statement:
--   The Log Compress construction uses the compress diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L47-L54

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

theorem GlobalTheory.LogCompress.compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by sorry
