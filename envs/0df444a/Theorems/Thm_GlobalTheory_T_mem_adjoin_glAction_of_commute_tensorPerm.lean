-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_adjoin_glAction_of_commute_tensorPerm
-- name    : GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:27.325868+00:00
-- url     : https://prove2.me/theorems/e4f28e26-1ed2-4cbc-8081-28355b920bf4
-- title:
--   T: mem adjoin gl Action of commute tensor Perm
-- statement:
--   The T construction uses the mem adjoin gl Action of commute tensor Perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPermStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemAdjoinGlActionOfCommuteTensorPermStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm : ∀ (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ π, T * permMat n d π = permMat n d π * T) → T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by sorry
