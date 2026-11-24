-- Prove2me | Theorems.Thm_GlobalTheory_SymmTensor_mem_adjoin_polar
-- name    : GlobalTheory.SymmTensor.mem_adjoin_polar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:56.941292+00:00
-- url     : https://prove2.me/theorems/2d13c43b-55bb-4569-b754-0c68ebfa8050
-- title:
--   Symm Tensor: mem adjoin polar
-- statement:
--   The Symm Tensor construction uses the mem adjoin polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L122-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPerm.lean#L122-L140

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

theorem GlobalTheory.SymmTensor.mem_adjoin_polar (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by sorry
