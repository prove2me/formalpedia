-- Prove2me | Theorems.Thm_GlobalTheory_T_bicommutant_tensorFactorPerm_mem_span
-- name    : GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:30.240812+00:00
-- url     : https://prove2.me/theorems/b7b8a092-41d1-4436-8a37-22a1a487a3b5
-- title:
--   T: bicommutant tensor Factor Perm mem span
-- statement:
--   The T construction uses the bicommutant tensor Factor Perm mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BicommutantTensorFactorPermMemSpanStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BicommutantTensorFactorPermMemSpanStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
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

theorem GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by sorry
