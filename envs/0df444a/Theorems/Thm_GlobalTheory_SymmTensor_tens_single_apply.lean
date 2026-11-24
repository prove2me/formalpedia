-- Prove2me | Theorems.Thm_GlobalTheory_SymmTensor_tens_single_apply
-- name    : GlobalTheory.SymmTensor.tens_single_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:43.972149+00:00
-- url     : https://prove2.me/theorems/45aabb1c-12b8-430e-a64d-dc5313c16272
-- title:
--   Symm Tensor: tens single apply
-- statement:
--   The Symm Tensor construction uses the tens single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L30-L38

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

theorem GlobalTheory.SymmTensor.tens_single_apply (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by sorry
