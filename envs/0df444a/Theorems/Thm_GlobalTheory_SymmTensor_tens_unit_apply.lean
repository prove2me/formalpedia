-- Prove2me | Theorems.Thm_GlobalTheory_SymmTensor_tens_unit_apply
-- name    : GlobalTheory.SymmTensor.tens_unit_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:36.011652+00:00
-- url     : https://prove2.me/theorems/9c9d3ee3-13a8-4b0b-9226-6a6efd8faaa8
-- title:
--   Symm Tensor: tens unit apply
-- statement:
--   The Symm Tensor construction uses the tens unit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L113-L120

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

theorem GlobalTheory.SymmTensor.tens_unit_apply (I K I' K' : Fin d → Fin n) (π : Equiv.Perm (Fin d)) :
    tens ((fun p => Matrix.single (I p) (K p) (1 : ℂ)) ∘ π) I' K' =
      if I = I' ∘ π.symm then if K = K' ∘ π.symm then 1 else 0 else 0 := by sorry
