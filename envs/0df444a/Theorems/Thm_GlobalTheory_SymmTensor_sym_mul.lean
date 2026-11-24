-- Prove2me | Theorems.Thm_GlobalTheory_SymmTensor_sym_mul
-- name    : GlobalTheory.SymmTensor.sym_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:45.005417+00:00
-- url     : https://prove2.me/theorems/613ac6ed-b467-45f5-a9a2-e7e24b1b75b1
-- title:
--   Symm Tensor: sym mul
-- statement:
--   The Symm Tensor construction uses the sym mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L55-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SymmTensor
variable {n d : ℕ}

theorem GlobalTheory.SymmTensor.sym_mul (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    sym X * ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ i : Fin d, sym (X * Pi.mulSingle i Y) := by sorry
