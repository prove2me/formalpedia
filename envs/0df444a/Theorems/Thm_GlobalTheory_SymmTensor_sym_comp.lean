-- Prove2me | Theorems.Thm_GlobalTheory_SymmTensor_sym_comp
-- name    : GlobalTheory.SymmTensor.sym_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:42.116261+00:00
-- url     : https://prove2.me/theorems/6a935f25-6b9f-45b5-a615-9ebaeb3c2107
-- title:
--   Symm Tensor: sym comp
-- statement:
--   The Symm Tensor construction uses the sym comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L52-L53

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

theorem GlobalTheory.SymmTensor.sym_comp (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X := by sorry
