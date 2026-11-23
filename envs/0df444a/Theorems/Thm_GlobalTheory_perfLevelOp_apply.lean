-- Prove2me | Theorems.Thm_GlobalTheory_perfLevelOp_apply
-- name    : GlobalTheory.perfLevelOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:00.98198+00:00
-- url     : https://prove2.me/theorems/632a4f35-c4cd-49dd-8f77-8f8d0ca01b6b
-- title:
--   Global Theory: perf Level Op apply
-- statement:
--   The Global Theory construction uses the perf Level Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PerfectionExistsUniqueSubMatrixFrobeniusEq.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PerfectionExistsUniqueSubMatrixFrobeniusEq.lean#L38-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.perfLevelOp_apply (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    perfLevelOp p S Q n w = (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k) := by sorry
