-- Prove2me | Theorems.Thm_GlobalTheory_LogCompress_jensen_exp
-- name    : GlobalTheory.LogCompress.jensen_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:17:00.374913+00:00
-- url     : https://prove2.me/theorems/22f1b00a-95f9-411e-92ec-626fda6e1e23
-- title:
--   Log Compress: jensen exp
-- statement:
--   The Log Compress construction uses the jensen exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L8-L45

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

theorem GlobalTheory.LogCompress.jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by sorry
